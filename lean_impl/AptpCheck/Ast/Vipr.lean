import AptpCheck.Ast.Sexpr
import AptpCheck.Cert.LinCon

/-!
# VIPR v1.0 certificate parser

Reads a `.vipr` certificate (ASCII, token-oriented) into a structured
`Vipr` value.  Sections in order: `VER / VAR / INT / OBJ / CON / RTP / SOL / DER`.
Numbers are exact rationals — decimal (`-2.5`, `.5`, reusing `Ast.parseRat?`) or
`p/q` (handled here by `parseNum?`).

The heart is the `DER` list of derived constraints, each with a *reason*
(`asm`, `lin`, `rnd`, `uns`, `sol`).  The constraint/derived-constraint body is the
same in both `CON` and `DER`: either an explicit sparse form `p i₁ a₁ … iₚ aₚ` or
the keyword `OBJ`.

`conLes` / `senseToLes` normalize a parsed constraint to the `Le` representation of
`AptpCheck.Cert.LinCon` (`G` by negation, `E` as two `Le`s), so the parser output
feeds directly into the `Cert/Vipr` replay checker.

The `SOL` section is parsed best-effort (name + nonzero list); it is not needed for
the `RTP infeas` acceptance check.
-/

namespace AptpCheck.Ast

open AptpCheck.Cert

/-! ## Number parsing (integers and `p/q` rationals) -/

/-- Parse a signed integer literal. -/
def parseInt? (s : String) : Option ℤ :=
  match s.toList with
  | '-' :: rest => (natOfDigits? rest).map (fun n => -(n : ℤ))
  | '+' :: rest => (natOfDigits? rest).map (fun n => (n : ℤ))
  | cs          => (natOfDigits? cs).map (fun n => (n : ℤ))

/-- Parse an exact rational: either a decimal literal (`Ast.parseRat?`) or `p/q`. -/
def parseNum? (s : String) : Option ℚ :=
  match splitOnChar '/' s.toList with
  | [_] => parseRat? s
  | [num, den] =>
      match parseInt? (String.ofList num), natOfDigits? den with
      | some p, some q => if q == 0 then none else some ((p : ℚ) / (q : ℚ))
      | _, _ => none
  | _ => none

/-! ## Parsed AST -/

/-- A `CON` constraint: `name sense rhs (form | OBJ)`. -/
structure ViprCon where
  name : String
  sense : Char        -- 'E' (=), 'L' (≤), 'G' (≥)
  rhs : ℚ
  form : LinForm      -- explicit sparse form; empty when `usesObj`
  usesObj : Bool      -- form is the objective row
  deriving Repr, Inhabited

/-- The justification of a derived constraint. `lin`/`rnd` carry `(index, multiplier)`
pairs referencing earlier constraints; `uns` carries four earlier indices. -/
inductive ViprReason where
  | asm
  | lin (terms : List (Nat × ℚ))
  | rnd (terms : List (Nat × ℚ))
  | uns (i1 l1 i2 l2 : Nat)
  | sol
  deriving Repr, Inhabited

/-- A `DER` derived constraint: `name sense rhs (form | OBJ) { reason } finalUseIdx`. -/
structure ViprDer where
  name : String
  sense : Char
  rhs : ℚ
  form : LinForm
  usesObj : Bool
  reason : ViprReason
  idx : Int            -- trailing final-use index (`-1` = unused)
  deriving Repr, Inhabited

/-- The `RTP` (relation-to-prove) target. -/
inductive ViprRtp where
  | infeas
  | range (lb ub : Option ℚ)   -- `none` = unbounded (`inf` / `-inf`)
  deriving Repr, Inhabited

/-- A parsed VIPR certificate. -/
structure Vipr where
  version : String
  varNames : Array String
  intVars : List Nat
  objSense : String              -- "min" / "max"
  objTerms : List (Nat × ℚ)
  numCon : Nat
  numBounds : Nat
  cons : Array ViprCon
  rtp : ViprRtp
  numSol : Nat
  sols : Array (String × List (Nat × ℚ))
  ders : Array ViprDer
  deriving Repr, Inhabited

/-! ## Tokenizer -/

/-- Split into whitespace-separated tokens (drops empty runs). VIPR pads its
structural tokens (`{`, `}`) with whitespace, so a whitespace split is faithful. -/
def wsTokens (input : List Char) : List String := Id.run do
  let mut toks : List String := []
  let mut cur : List Char := []
  for c in input do
    if c.isWhitespace then
      if !cur.isEmpty then toks := String.ofList cur.reverse :: toks; cur := []
    else
      cur := c :: cur
  if !cur.isEmpty then toks := String.ofList cur.reverse :: toks
  return toks.reverse

/-! ## Token consumers (Except-monad parser over `List String`) -/

abbrev Toks := List String

def takeTok : Toks → Except String (String × Toks)
  | [] => Except.error "unexpected end of input"
  | t :: ts => Except.ok (t, ts)

def expectTok (s : String) (ts : Toks) : Except String Toks :=
  match ts with
  | [] => Except.error s!"expected '{s}', got end of input"
  | t :: ts' => if t == s then Except.ok ts' else Except.error s!"expected '{s}', got '{t}'"

def takeNat (ts : Toks) : Except String (Nat × Toks) := do
  let (t, ts') ← takeTok ts
  match natOfDigits? t.toList with
  | some n => Except.ok (n, ts')
  | none   => Except.error s!"expected nat, got '{t}'"

def takeInt (ts : Toks) : Except String (Int × Toks) := do
  let (t, ts') ← takeTok ts
  match parseInt? t with
  | some n => Except.ok (n, ts')
  | none   => Except.error s!"expected int, got '{t}'"

def takeNum (ts : Toks) : Except String (ℚ × Toks) := do
  let (t, ts') ← takeTok ts
  match parseNum? t with
  | some q => Except.ok (q, ts')
  | none   => Except.error s!"expected number, got '{t}'"

def takeSense (ts : Toks) : Except String (Char × Toks) := do
  let (t, ts') ← takeTok ts
  match t.toList with
  | ['E'] => Except.ok ('E', ts')
  | ['L'] => Except.ok ('L', ts')
  | ['G'] => Except.ok ('G', ts')
  | _     => Except.error s!"expected sense E/L/G, got '{t}'"

/-- Read `n` `(index value)` pairs. -/
def takePairs : Nat → Toks → Except String (List (Nat × ℚ) × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (i, ts1) ← takeNat ts
      let (c, ts2) ← takeNum ts1
      let (rest, ts3) ← takePairs n ts2
      Except.ok ((i, c) :: rest, ts3)

/-- Read `n` natural-number tokens. -/
def takeNats : Nat → Toks → Except String (List Nat × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (i, ts1) ← takeNat ts
      let (rest, ts2) ← takeNats n ts1
      Except.ok (i :: rest, ts2)

/-- Read `n` raw tokens (variable names). -/
def takeStrings : Nat → Toks → Except String (List String × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (s, ts1) ← takeTok ts
      let (rest, ts2) ← takeStrings n ts1
      Except.ok (s :: rest, ts2)

/-- Read a constraint body: `p i₁ a₁ … iₚ aₚ` (returns the form) or `OBJ`. -/
def takeBody (ts : Toks) : Except String ((LinForm × Bool) × Toks) := do
  let (t, ts') ← takeTok ts
  if t == "OBJ" then
    Except.ok (([], true), ts')
  else
    match natOfDigits? t.toList with
    | some p => do
        let (pairs, ts2) ← takePairs p ts'
        Except.ok ((pairs.map (fun q => (⟨q.1, q.2⟩ : Term)), false), ts2)
    | none => Except.error s!"expected count or OBJ, got '{t}'"

def takeCon (ts : Toks) : Except String (ViprCon × Toks) := do
  let (name, ts1) ← takeTok ts
  let (sense, ts2) ← takeSense ts1
  let (rhs, ts3) ← takeNum ts2
  let ((form, usesObj), ts4) ← takeBody ts3
  Except.ok ({ name := name, sense := sense, rhs := rhs, form := form,
               usesObj := usesObj }, ts4)

def takeCons : Nat → Toks → Except String (List ViprCon × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (c, ts1) ← takeCon ts
      let (rest, ts2) ← takeCons n ts1
      Except.ok (c :: rest, ts2)

/-- Read a `{ reason }` block. -/
def takeReason (ts : Toks) : Except String (ViprReason × Toks) := do
  let ts1 ← expectTok "{" ts
  let (kw, ts2) ← takeTok ts1
  match kw with
  | "asm" => do let ts3 ← expectTok "}" ts2; Except.ok (ViprReason.asm, ts3)
  | "sol" => do let ts3 ← expectTok "}" ts2; Except.ok (ViprReason.sol, ts3)
  | "lin" => do
      let (p, ts3) ← takeNat ts2
      let (pairs, ts4) ← takePairs p ts3
      let ts5 ← expectTok "}" ts4
      Except.ok (ViprReason.lin pairs, ts5)
  | "rnd" => do
      let (p, ts3) ← takeNat ts2
      let (pairs, ts4) ← takePairs p ts3
      let ts5 ← expectTok "}" ts4
      Except.ok (ViprReason.rnd pairs, ts5)
  | "uns" => do
      let (i1, ts3) ← takeNat ts2
      let (l1, ts4) ← takeNat ts3
      let (i2, ts5) ← takeNat ts4
      let (l2, ts6) ← takeNat ts5
      let ts7 ← expectTok "}" ts6
      Except.ok (ViprReason.uns i1 l1 i2 l2, ts7)
  | _ => Except.error s!"unknown reason '{kw}'"

def takeDer (ts : Toks) : Except String (ViprDer × Toks) := do
  let (name, ts1) ← takeTok ts
  let (sense, ts2) ← takeSense ts1
  let (rhs, ts3) ← takeNum ts2
  let ((form, usesObj), ts4) ← takeBody ts3
  let (reason, ts5) ← takeReason ts4
  let (idx, ts6) ← takeInt ts5
  -- SCIP marks some derivations as globally/locally valid with a trailing keyword;
  -- consume it if present (it carries no information the checker needs).
  let ts7 := match ts6 with
    | "global" :: rest => rest
    | "local"  :: rest => rest
    | _ => ts6
  Except.ok ({ name := name, sense := sense, rhs := rhs, form := form,
               usesObj := usesObj, reason := reason, idx := idx }, ts7)

def takeDers : Nat → Toks → Except String (List ViprDer × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (d, ts1) ← takeDer ts
      let (rest, ts2) ← takeDers n ts1
      Except.ok (d :: rest, ts2)

/-- Read one solution: `name p i₁ v₁ … iₚ vₚ` (best-effort). -/
def takeSol (ts : Toks) : Except String ((String × List (Nat × ℚ)) × Toks) := do
  let (name, ts1) ← takeTok ts
  let (p, ts2) ← takeNat ts1
  let (pairs, ts3) ← takePairs p ts2
  Except.ok ((name, pairs), ts3)

def takeSols : Nat → Toks → Except String (List (String × List (Nat × ℚ)) × Toks)
  | 0,     ts => Except.ok ([], ts)
  | (n+1), ts => do
      let (s, ts1) ← takeSol ts
      let (rest, ts2) ← takeSols n ts1
      Except.ok (s :: rest, ts2)

/-! ## Top-level parser -/

def parseVipr (content : String) : Except String Vipr := do
  let ts0 := wsTokens content.toList
  let ts1 ← expectTok "VER" ts0
  let (ver, ts2) ← takeTok ts1
  let ts3 ← expectTok "VAR" ts2
  let (nvar, ts4) ← takeNat ts3
  let (names, ts5) ← takeStrings nvar ts4
  let ts6 ← expectTok "INT" ts5
  let (nint, ts7) ← takeNat ts6
  let (ints, ts8) ← takeNats nint ts7
  let ts9 ← expectTok "OBJ" ts8
  let (objsense, ts10) ← takeTok ts9
  let (nobj, ts11) ← takeNat ts10
  let (objterms, ts12) ← takePairs nobj ts11
  let ts13 ← expectTok "CON" ts12
  let (ncon, ts14) ← takeNat ts13
  let (nbound, ts15) ← takeNat ts14
  let (cons, ts16) ← takeCons ncon ts15
  let ts17 ← expectTok "RTP" ts16
  let (rtpkind, ts18) ← takeTok ts17
  let (rtp, ts19) ←
    if rtpkind == "infeas" then
      (Except.ok (ViprRtp.infeas, ts18) : Except String (ViprRtp × Toks))
    else if rtpkind == "range" then do
      let (lb, tsa) ← takeTok ts18
      let (ub, tsb) ← takeTok tsa
      Except.ok (ViprRtp.range (parseNum? lb) (parseNum? ub), tsb)
    else
      Except.error s!"unknown RTP kind '{rtpkind}'"
  let ts20 ← expectTok "SOL" ts19
  let (nsol, ts21) ← takeNat ts20
  let (sols, ts22) ← takeSols nsol ts21
  let ts23 ← expectTok "DER" ts22
  let (nder, ts24) ← takeNat ts23
  let (ders, _ts25) ← takeDers nder ts24
  Except.ok {
    version := ver,
    varNames := names.toArray,
    intVars := ints,
    objSense := objsense,
    objTerms := objterms,
    numCon := ncon,
    numBounds := nbound,
    cons := cons.toArray,
    rtp := rtp,
    numSol := nsol,
    sols := sols.toArray,
    ders := ders.toArray }

/-! ## Bridge to the `Le` representation of `Cert/LinCon` -/

/-- Negate every coefficient of a form (used to normalize `G`/`E` rows). -/
def negForm (f : LinForm) : LinForm := f.map (fun t => (⟨t.idx, -t.coeff⟩ : Term))

/-- Normalize a sensed row to `≤`-form `Le`s: `L` as-is, `G` negated, `E` as two. -/
def senseToLes (sense : Char) (form : LinForm) (rhs : ℚ) : List Le :=
  match sense with
  | 'L' => [⟨form, rhs⟩]
  | 'G' => [⟨negForm form, -rhs⟩]
  | 'E' => [⟨form, rhs⟩, ⟨negForm form, -rhs⟩]
  | _   => []

/-- Resolve a `CON` constraint's linear form, substituting the objective row when the
constraint uses `OBJ`. -/
def ViprCon.resolvedForm (c : ViprCon) (objTerms : List (Nat × ℚ)) : LinForm :=
  if c.usesObj then objTerms.map (fun q => (⟨q.1, q.2⟩ : Term)) else c.form

/-- All `CON` rows of a certificate as `Le`s (objective references resolved). -/
def Vipr.conLes (v : Vipr) : List Le :=
  (v.cons.toList).flatMap (fun c => senseToLes c.sense (c.resolvedForm v.objTerms) c.rhs)

end AptpCheck.Ast
