import AptpCheck.Ast.Sexpr

/-!
# `.aptp` proof-file parser

Parses the SMT-LIB-flavored APTP format into a `Problem`: the input box, the
output objective rows `(c, rhs)`, the declared hidden `ReLU` neurons, and the
proof-tree `leaves` (each a list of signed neuron ids: `+k` active, `−k`
inactive). Mirrors the reference `read_aptp.py`. Supports both single- and
multi-name `declare-*` forms.
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

/-- Parse one `(and (op N_k 0) …)` clause into a leaf (list of signed neuron ids).
Items whose right-hand side is an output variable are skipped (defensive, as in
the reference). -/
def mkLeaf (clause : Sexp) : Except String (Array Int) :=
  match clause with
  | .list (.atom "and" :: items) => Id.run do
      let mut leaf : Array Int := #[]
      for it in items do
        match it with
        | .list [.atom op, .atom neuron, .atom point] =>
            match point.toList with
            | 'Y' :: _ => pure ()
            | _ =>
              match parseVarName neuron, parseRat? point with
              | some ('N', k), some z =>
                  if z ≠ 0 then return .error "split point must be 0"
                  else if op == ">=" then leaf := leaf.push (Int.ofNat k)
                  else if op == "<" then leaf := leaf.push (-(Int.ofNat k))
                  else return .error s!"bad hidden op: {op}"
              | _, _ => return .error s!"bad clause item near {neuron} {point}"
        | _ => return .error "malformed clause item"
      return .ok leaf
  | _ => .error "expected (and …) clause"

/-- Parse a `.aptp` file into a `Problem`. -/
def parseAptp (content : String) : Except String Problem :=
  match readStatements content with
  | .error e => .error e
  | .ok raw => Id.run do
    let mut sexps : Array Sexp := #[]
    for l in raw do
      match parseStatement l with
      | some e => sexps := sexps.push e
      | none => return .error "S-expression parse error"
    -- pass 1: declarations
    let mut maxIn : Int := -1
    let mut maxOut : Int := -1
    let mut neurons : Array Nat := #[]
    for e in sexps do
      match e with
      | .list (.atom "declare-const" :: rest) =>
          for nm in rest.dropLast do
            match nm with
            | .atom s =>
                match parseVarName s with
                | some ('X', i) => maxIn := max maxIn (Int.ofNat i)
                | some ('Y', i) => maxOut := max maxOut (Int.ofNat i)
                | _ => return .error s!"bad declare-const name: {s}"
            | _ => return .error "malformed declare-const"
      | .list (.atom "declare-pwl" :: rest) =>
          for nm in rest.dropLast do
            match nm with
            | .atom s =>
                match parseVarName s with
                | some ('N', i) => neurons := neurons.push i
                | _ => return .error s!"bad declare-pwl name: {s}"
            | _ => return .error "malformed declare-pwl"
      | _ => pure ()
    let numInputs := (maxIn + 1).toNat
    let numOutputs := (maxOut + 1).toNat
    -- pass 2: asserts
    let mut lo : Array (Option ℚ) := (List.replicate numInputs (none : Option ℚ)).toArray
    let mut hi : Array (Option ℚ) := (List.replicate numInputs (none : Option ℚ)).toArray
    let mut objs : Array Objective := #[]
    let mut leaves : Array (Array Int) := #[]
    for e in sexps do
      match e with
      | .list [.atom "assert", body] =>
          match body with
          | .list [.atom op, .atom a, .atom b] =>
              match asBoxUpdate op a b with
              | some (i, isUpper, v) =>
                  if isUpper then
                    hi := hi.set! i (some (match hi[i]! with | some h => min h v | none => v))
                  else
                    lo := lo.set! i (some (match lo[i]! with | some l => max l v | none => v))
              | none =>
                  match asObjective numOutputs op a b with
                  | some ob => objs := objs.push ob
                  | none => return .error s!"unsupported assert: ({op} {a} {b})"
          | .list (.atom "or" :: clauses) =>
              for clause in clauses do
                match mkLeaf clause with
                | .ok leaf => if !leaf.isEmpty then leaves := leaves.push leaf
                | .error er => return .error er
          | _ => return .error "unsupported assert body"
      | _ => pure ()
    -- finalize box
    let mut box : Array (ℚ × ℚ) := #[]
    for i in [0:numInputs] do
      match lo[i]!, hi[i]! with
      | some l, some h => box := box.push (l, h)
      | _, _ => return .error s!"input X_{i} is unbounded"
    return .ok { numInputs := numInputs, numOutputs := numOutputs,
                 neurons := neurons, box := box, objectives := objs, leaves := leaves }

end AptpCheck.Ast
