import LeanVIPR.Ast.Vipr
import LeanVIPR.Cert.ViprSem

/-!
# Parsed VIPR certificates and the executable checker

This module maps the parsed `CON` and `DER` records directly to the sensed
constraint representation used by the verified checker. VIPR indices match the
pool indices because equality rows remain single sensed rows.
-/

namespace LeanVIPR.Pipeline

open LeanVIPR.Cert LeanVIPR.Ast

/-- Resolve one parsed constraint to the sensed representation used by the checker. -/
def conToSLe (v : Vipr) (c : ViprCon) : SLe :=
  ⟨c.sense, c.resolvedForm v.objTerms, c.rhs⟩

/-- The sensed constraint rows of the certificate, with objective references resolved. -/
def conSLes (v : Vipr) : List SLe :=
  v.cons.toList.map (conToSLe v)

/-- Resolve a derivation's stated form, substituting the objective when requested. -/
def derForm (v : Vipr) (d : ViprDer) : LinForm :=
  if d.usesObj then v.objTerms.map (fun q => (⟨q.1, q.2⟩ : Term)) else d.form

/-- Resolve one parsed derivation's stated row. -/
def derStated (v : Vipr) (d : ViprDer) : SLe :=
  ⟨d.sense, derForm v d, d.rhs⟩

/-- Lookup a certificate row by its VIPR index. References to malformed indices use the
same harmless default row as the replay pool and are subsequently rejected by the
references-past check. -/
def viprRow (v : Vipr) (idx : Nat) : SLe :=
  if h : idx < v.cons.size then
    conToSLe v v.cons[idx]
  else
    let derIdx := idx - v.cons.size
    if hder : derIdx < v.ders.size then derStated v v.ders[derIdx] else sdflt.1

/-- Coefficient of one variable after combining duplicate sparse terms. -/
def formCoeff (form : LinForm) (idx : Nat) : ℚ :=
  form.foldl (fun coeff term => if term.idx = idx then coeff + term.coeff else coeff) 0

/-- The normalized row contains no nonzero coefficient except possibly at `idx`. -/
def onlyVarB (form : LinForm) (idx : Nat) : Bool :=
  (normForm form).all (fun term => decide (term.1 = idx ∨ term.2 = 0))

/-- Does `row` express a lower (`L`) or upper (`U`) bound on variable `idx`? -/
def boundRowB (row : SLe) (kind : Char) (idx : Nat) : Bool :=
  let coeff := formCoeff row.form idx
  onlyVarB row.form idx && decide (coeff ≠ 0) &&
    if kind = 'L' then
      (row.sense = 'G' && 0 < coeff) || (row.sense = 'L' && coeff < 0)
    else if kind = 'U' then
      (row.sense = 'L' && 0 < coeff) || (row.sense = 'G' && coeff < 0)
    else
      false

/-- Rows eligible for SCIP's global-bound table before derivation `derIdx`.

Every original one-variable constraint is eligible. An earlier derived row is eligible
only when SCIP marked it `global`. -/
def globalBoundIndices (v : Vipr) (derIdx : Nat) : List Nat :=
  List.range v.cons.size ++
    (List.range (min derIdx v.ders.size)).filterMap fun idx =>
      if (v.ders.getD idx default).isGlobal then some (v.cons.size + idx) else none

/-- Find the tightest matching global bound available before derivation `derIdx`. -/
def globalBoundRef? (v : Vipr) (derIdx : Nat) (kind : Char) (idx : Nat) : Option Nat :=
  let boundIndices := globalBoundIndices v derIdx
  let best := boundIndices.foldl (fun best rowIdx =>
    let row := viprRow v rowIdx
    let coeff := formCoeff row.form idx
    if boundRowB row kind idx then
      let value := row.rhs / coeff
      match best with
      | none => some (rowIdx, value)
      | some current =>
          if (kind = 'L' && current.2 < value) || (kind = 'U' && value < current.2) then
            some (rowIdx, value)
          else
            best
    else
      best) none
  best.map Prod.fst

/-- Find the explicitly listed local bound for a variable, checking that the referenced
row really expresses the declared bound value. If no local bound is listed, fall back to
the current global bound table as prescribed by the v1.1 completion algorithm. -/
def weakBoundRef? (v : Vipr) (derIdx : Nat) (bounds : ViprWeakBounds) (kind : Char)
    (idx : Nat) : Option Nat :=
  match bounds with
  | .global => globalBoundRef? v derIdx kind idx
  | .local localBounds =>
      match localBounds.find? (fun bound => bound.kind = kind && bound.varIdx = idx) with
      | some bound =>
          let row := viprRow v bound.rowIdx
          let coeff := formCoeff row.form idx
          if boundRowB row kind idx && decide (row.rhs = coeff * bound.value) then
            some bound.rowIdx
          else
            none
      | none => globalBoundRef? v derIdx kind idx

/-- Which variable-bound direction repairs coefficient `delta` while preserving the
sense of the stated row? -/
def correctionKind? (sense : Char) (delta : ℚ) : Option Char :=
  if delta = 0 then
    none
  else if sense = 'L' then
    some (if delta < 0 then 'L' else 'U')
  else if sense = 'G' then
    some (if 0 < delta then 'L' else 'U')
  else
    none

/-- Complete a VIPR v1.1 `lin weak` reason with variable-bound rows.

This function only proposes an ordinary `lin` combination. The existing `linCheck`
recomputes that combination from the actual referenced rows and rejects any malformed
or insufficient completion, so checker soundness does not trust this algorithm. -/
def completeWeakComb (v : Vipr) (derIdx : Nat) (stated : SLe) (bounds : ViprWeakBounds)
    (terms : List (Nat × ℚ)) : List (ℚ × Nat) :=
  let baseComb := terms.map (fun term => (term.2, term.1))
  let combined := scomb (baseComb.map (fun term => (term.1, viprRow v term.2)))
  let corrections := (List.range v.varNames.size).filterMap fun idx =>
    let delta := formCoeff stated.form idx - formCoeff combined.form idx
    match correctionKind? stated.sense delta with
    | none => none
    | some kind =>
        match weakBoundRef? v derIdx bounds kind idx with
        | none => none
        | some rowIdx =>
            let coeff := formCoeff (viprRow v rowIdx).form idx
            if coeff = 0 then none else some (delta / coeff, rowIdx)
  baseComb ++ corrections

/-- Interpret one parsed derivation as a sensed checker step. -/
def derToSStep (v : Vipr) (derIdx : Nat) (d : ViprDer) : SStep :=
  { stated := derStated v d
    reason := match d.reason with
      | .asm => .asm
      | .lin terms => .lin (terms.map (fun p => (p.2, p.1)))
      | .linWeak bounds terms =>
          .lin (completeWeakComb v derIdx (derStated v d) bounds terms)
      | .rnd terms => .rnd (terms.map (fun p => (p.2, p.1)))
      | .uns i1 l1 i2 l2 => .uns i1 l1 i2 l2
      | .sol => .sol }

def viprSteps (v : Vipr) : List SStep :=
  v.ders.toList.mapIdx (derToSStep v)

end LeanVIPR.Pipeline
