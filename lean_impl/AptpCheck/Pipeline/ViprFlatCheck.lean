import AptpCheck.Cert.ViprFlat
import AptpCheck.Cert.ViprSem
import AptpCheck.Ast.Vipr

/-!
# Verified flat check on a parsed VIPR certificate (no reshaper)

`checkVipr` reads the parsed derivation records `v.ders` and constraint rows
`v.conLes` **directly** and re-validates them with the proven `checkFlat`. There is no
intermediate tree and no separately-trusted converter: the record interpretation
(`reasonToF`) lives inside the checker, and `checkVipr_sound` proves that acceptance
implies the certificate's *own* CON rows are infeasible. A misinterpretation by the
reader can therefore only cause a spurious rejection, never a false "certified".

Index convention: a VIPR index coincides with the flat pool index when the `CON`
section has no equalities (each inequality contributes exactly one `Le`); the encoder
in the assembled tool emits inequalities, so this holds on its certificates.
-/

namespace AptpCheck.Pipeline

open AptpCheck.Cert AptpCheck.Ast

/-- The `Le` a VIPR index denotes: `CON` rows (`0..numCon-1`) then `DER` rows, taking
the head of the sensed normalization (bounds normalize to a single `Le`). -/
def viprRow (v : Vipr) (i : Nat) : Le :=
  if i < v.numCon then
    let c := v.cons.getD i default
    (senseToLes c.sense (c.resolvedForm v.objTerms) c.rhs).headD ⟨[], 0⟩
  else
    let d := v.ders.getD (i - v.numCon) default
    (senseToLes d.sense d.form d.rhs).headD ⟨[], 0⟩

/-- Interpret one parsed derivation record as a flat step. This is the *reader*; its
output is re-validated by `checkFlat`, so any misreading only causes a spurious reject.
For `uns`, the split variable/point are recovered from the lower-bound assumption row. -/
def reasonToF (v : Vipr) (d : ViprDer) : FReason :=
  match d.reason with
  | .asm       => .asm ((senseToLes d.sense d.form d.rhs).headD ⟨[], 0⟩)
  | .lin terms => .lin (terms.map (fun p => (p.2, p.1)))
  | .rnd terms => .rnd (terms.map (fun p => (p.2, p.1)))
  | .uns i1 l1 i2 l2 =>
      let lo := viprRow v l1
      let j := (lo.form.head?).elim 0 (fun t => t.idx)
      .uns i1 i2 j lo.rhs.num
  | .sol       => .lin []

/-- Read the whole derivation list into flat steps. -/
def viprSteps (v : Vipr) : List FReason := v.ders.toList.map (reasonToF v)

/-- Verified flat check on a parsed VIPR certificate. -/
def checkVipr (v : Vipr) : Bool := checkFlat v.intVars v.conLes (viprSteps v)

/-- **Soundness of the direct VIPR check.** If `checkVipr` accepts, no valuation with
the declared integer variables integral satisfies the certificate's own CON rows. The
record interpretation is inside the verified path — no separately-trusted converter. -/
theorem checkVipr_sound (v : Vipr) (h : checkVipr v = true) :
    ∀ a, (∀ j ∈ v.intVars, IsIntVal (a j)) → (∀ c ∈ v.conLes, Le.sat c a) → False :=
  checkFlat_sound v.intVars v.conLes (viprSteps v) h

/-! ## Full VIPR v1.0 semantics checker (`checkSem`) — accepts real solver certificates -/

/-- The sensed constraint rows of the certificate (one `SLe` per `CON` entry, objective
resolved). Unlike `conLes`, `E` rows are *not* split, so VIPR indices match pool indices. -/
def conSLes (v : Vipr) : List SLe :=
  v.cons.toList.map (fun c => ⟨c.sense, c.resolvedForm v.objTerms, c.rhs⟩)

/-- Resolve a derivation's stated form (objective substituted when `usesObj`). -/
def derForm (v : Vipr) (d : ViprDer) : LinForm :=
  if d.usesObj then v.objTerms.map (fun q => (⟨q.1, q.2⟩ : Term)) else d.form

/-- Interpret one parsed derivation as a sensed step (indices already match the pool). -/
def derToSStep (v : Vipr) (d : ViprDer) : SStep :=
  { stated := ⟨d.sense, derForm v d, d.rhs⟩,
    reason := match d.reason with
      | .asm => .asm
      | .lin terms => .lin (terms.map (fun p => (p.2, p.1)))
      | .rnd terms => .rnd (terms.map (fun p => (p.2, p.1)))
      | .uns i1 l1 i2 l2 => .uns i1 l1 i2 l2
      | .sol => .lin [] }

def viprSteps2 (v : Vipr) : List SStep := v.ders.toList.map (derToSStep v)

/-- The full-semantics verified checker: reads the parsed VIPR records directly. -/
def checkSem (v : Vipr) : Bool := checkSemCore v.intVars (conSLes v) (viprSteps2 v)

/-- **Soundness of `checkSem`.** Acceptance implies the certificate's own (sensed) CON
rows are infeasible over the integer-declared variables. -/
theorem checkSem_sound (v : Vipr) (h : checkSem v = true) :
    ∀ a, (∀ j ∈ v.intVars, IsIntVal (a j)) → (∀ c ∈ conSLes v, SLe.sat c a) → False :=
  checkSemCore_sound v.intVars (conSLes v) (viprSteps2 v) h

end AptpCheck.Pipeline
