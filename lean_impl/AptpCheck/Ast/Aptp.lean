import AptpCheck.Ast.Sexpr

/-!
# `.aptp` proof-file parser

Parses the SMT-LIB-flavored APTP format into a `Problem`: the input box, the
output objective rows `(c, rhs)`, the declared hidden `ReLU` neurons, and the
proof-tree `leaves` (each a list of signed neuron ids: `+k` active, `−k`
inactive). Mirrors the reference `read_aptp.py`. Supports both single- and
multi-name `declare-*` forms.

The statement/declaration/assert scans are written as **total `List.foldl`s over
an `Except`-carrying accumulator** (rather than `Id.run do` `for`-loops with early
`return`), so the kernel gets equational lemmas and the parser is amenable to the
faithfulness proofs in `Ast/AptpRoundtrip.lean`. Behaviour is identical to the
former loop form: each fold short-circuits on the first error and threads the
mutable state through the accumulator, exactly as the loops did.
-/

namespace AptpCheck.Ast

/-- One output-property row: `c · y {≤} rhs` (the checker proves `c · y > rhs`). -/
structure Objective where
  c : Array ℚ
  rhs : ℚ
  deriving Repr, Inhabited

structure Problem where
  numInputs : Nat
  numOutputs : Nat
  neurons : Array Nat
  box : Array (ℚ × ℚ)
  objectives : Array Objective
  leaves : Array (Array Int)
  deriving Repr, Inhabited

/-- Parse a declared variable name `P_i` into `(P, i)` (`P ∈ {X,Y,N}`). -/
def parseVarName (s : String) : Option (Char × Nat) :=
  match s.toList with
  | p :: '_' :: rest => (natOfDigits? rest).map (fun n => (p, n))
  | _ => none

/-- If `(op a b)` is a box constraint on some `X_i`, return `(i, isUpper, value)`. -/
def asBoxUpdate (op a b : String) : Option (Nat × Bool × ℚ) :=
  match parseVarName a with
  | some ('X', i) => (parseRat? b).map (fun v => (i, op == "<=", v))
  | _ => none

/-- If `(op a b)` is an output constraint, return the `(c, rhs)` row (normalized to `≤`). -/
def asObjective (numOutputs : Nat) (op a b : String) : Option Objective :=
  let zero : Array ℚ := (List.replicate numOutputs (0 : ℚ)).toArray
  let (first, second) := if op == ">=" then (b, a) else (a, b)
  match parseVarName first, parseVarName second with
  | some ('Y', i1), some ('Y', i2) =>
      some { c := (zero.set! i1 1).set! i2 (-1), rhs := 0 }
  | some ('Y', i1), _ => (parseRat? second).map (fun v => { c := zero.set! i1 1, rhs := v })
  | _, some ('Y', i2) => (parseRat? first).map (fun v => { c := zero.set! i2 (-1), rhs := -v })
  | _, _ => none

/-- Fold one `(and …)` clause item into the leaf accumulator (short-circuiting on
error). Items whose right-hand side is an output variable are skipped (defensive,
as in the reference). -/
def mkLeafStep (acc : Except String (Array Int)) (it : Sexp) : Except String (Array Int) :=
  match acc with
  | .error e => .error e
  | .ok leaf =>
    match it with
    | .list [.atom op, .atom neuron, .atom point] =>
        match point.toList with
        | 'Y' :: _ => .ok leaf
        | _ =>
          match parseVarName neuron, parseRat? point with
          | some ('N', k), some z =>
              if z ≠ 0 then .error "split point must be 0"
              else if op == ">=" then .ok (leaf.push (Int.ofNat k))
              else if op == "<" then .ok (leaf.push (-(Int.ofNat k)))
              else .error s!"bad hidden op: {op}"
          | _, _ => .error s!"bad clause item near {neuron} {point}"
    | _ => .error "malformed clause item"

/-- Parse one `(and (op N_k 0) …)` clause into a leaf (list of signed neuron ids). -/
def mkLeaf (clause : Sexp) : Except String (Array Int) :=
  match clause with
  | .list (.atom "and" :: items) => items.foldl mkLeafStep (.ok #[])
  | _ => .error "expected (and …) clause"

/-- Fold one statement into the parsed S-expression array (short-circuiting). -/
def parseAllStep (acc : Except String (Array Sexp)) (l : List Char) : Except String (Array Sexp) :=
  match acc with
  | .error e => .error e
  | .ok arr =>
    match parseStatement l with
    | some e => .ok (arr.push e)
    | none => .error "S-expression parse error"

/-- Fold one `declare-const` name into `(maxIn, maxOut)`. -/
def scanConstName (acc : Except String (Int × Int)) (nm : Sexp) : Except String (Int × Int) :=
  match acc with
  | .error er => .error er
  | .ok (maxIn, maxOut) =>
    match nm with
    | .atom s =>
        match parseVarName s with
        | some ('X', i) => .ok (max maxIn (Int.ofNat i), maxOut)
        | some ('Y', i) => .ok (maxIn, max maxOut (Int.ofNat i))
        | _ => .error s!"bad declare-const name: {s}"
    | _ => .error "malformed declare-const"

/-- Fold one `declare-pwl` name into the neuron-id array. -/
def scanPwlName (acc : Except String (Array Nat)) (nm : Sexp) : Except String (Array Nat) :=
  match acc with
  | .error er => .error er
  | .ok neurons =>
    match nm with
    | .atom s =>
        match parseVarName s with
        | some ('N', i) => .ok (neurons.push i)
        | _ => .error s!"bad declare-pwl name: {s}"
    | _ => .error "malformed declare-pwl"

/-- Fold one statement into `(maxIn, maxOut, neurons)` (declaration pass). -/
def scanDeclsStep (acc : Except String (Int × Int × Array Nat)) (e : Sexp) :
    Except String (Int × Int × Array Nat) :=
  match acc with
  | .error er => .error er
  | .ok (maxIn, maxOut, neurons) =>
    match e with
    | .list (.atom "declare-const" :: rest) =>
        match rest.dropLast.foldl scanConstName (.ok (maxIn, maxOut)) with
        | .error er => .error er
        | .ok (mi, mo) => .ok (mi, mo, neurons)
    | .list (.atom "declare-pwl" :: rest) =>
        match rest.dropLast.foldl scanPwlName (.ok neurons) with
        | .error er => .error er
        | .ok ns => .ok (maxIn, maxOut, ns)
    | _ => .ok (maxIn, maxOut, neurons)

/-- Fold one `(or …)`-clause into the leaves array (nonempty leaves only). -/
def scanClauseStep (acc : Except String (Array (Array Int))) (clause : Sexp) :
    Except String (Array (Array Int)) :=
  match acc with
  | .error er => .error er
  | .ok leaves =>
    match mkLeaf clause with
    | .ok leaf => if leaf.isEmpty then .ok leaves else .ok (leaves.push leaf)
    | .error er => .error er

/-- The assert-pass accumulator: per-input lower/upper bounds, objectives, leaves. -/
abbrev AssertState := Array (Option ℚ) × Array (Option ℚ) × Array Objective × Array (Array Int)

/-- Fold one statement into the assert state (box/objective/DNF pass). -/
def scanAssertsStep (numOutputs : Nat) (acc : Except String AssertState) (e : Sexp) :
    Except String AssertState :=
  match acc with
  | .error er => .error er
  | .ok (lo, hi, objs, leaves) =>
    match e with
    | .list [.atom "assert", body] =>
        match body with
        | .list [.atom op, .atom a, .atom b] =>
            match asBoxUpdate op a b with
            | some (i, isUpper, v) =>
                if isUpper then
                  .ok (lo, hi.set! i (some (match hi[i]! with | some h => min h v | none => v)), objs, leaves)
                else
                  .ok (lo.set! i (some (match lo[i]! with | some l => max l v | none => v)), hi, objs, leaves)
            | none =>
                match asObjective numOutputs op a b with
                | some ob => .ok (lo, hi, objs.push ob, leaves)
                | none => .error s!"unsupported assert: ({op} {a} {b})"
        | .list (.atom "or" :: clauses) =>
            match clauses.foldl scanClauseStep (.ok leaves) with
            | .error er => .error er
            | .ok leaves' => .ok (lo, hi, objs, leaves')
        | _ => .error "unsupported assert body"
    | _ => .ok (lo, hi, objs, leaves)

/-- Fold input index `i` into the finalized box (fails if `X_i` is unbounded). -/
def finalizeBoxStep (lo hi : Array (Option ℚ)) (acc : Except String (Array (ℚ × ℚ))) (i : Nat) :
    Except String (Array (ℚ × ℚ)) :=
  match acc with
  | .error er => .error er
  | .ok box =>
    match lo[i]!, hi[i]! with
    | some l, some h => .ok (box.push (l, h))
    | _, _ => .error s!"input X_{i} is unbounded"

/-- Parse a `.aptp` file into a `Problem`. -/
def parseAptp (content : String) : Except String Problem := do
  let raw ← readStatementsFold content
  let sexps ← raw.toList.foldl parseAllStep (.ok #[])
  let (maxIn, maxOut, neurons) ← sexps.toList.foldl scanDeclsStep (.ok (-1, -1, #[]))
  let numInputs := (maxIn + 1).toNat
  let numOutputs := (maxOut + 1).toNat
  let loInit : Array (Option ℚ) := (List.replicate numInputs (none : Option ℚ)).toArray
  let hiInit : Array (Option ℚ) := (List.replicate numInputs (none : Option ℚ)).toArray
  let (lo, hi, objs, leaves) ←
    sexps.toList.foldl (scanAssertsStep numOutputs) (.ok (loInit, hiInit, #[], #[]))
  let box ← (List.range numInputs).foldl (finalizeBoxStep lo hi) (.ok #[])
  .ok { numInputs := numInputs, numOutputs := numOutputs,
        neurons := neurons, box := box, objectives := objs, leaves := leaves }

end AptpCheck.Ast
