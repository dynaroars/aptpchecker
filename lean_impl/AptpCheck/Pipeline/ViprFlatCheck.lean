import AptpCheck.Cert.ViprFlat
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

end AptpCheck.Pipeline
