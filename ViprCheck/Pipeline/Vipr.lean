import ViprCheck.Ast.Vipr
import ViprCheck.Cert.ViprSem

/-!
# Parsed VIPR certificates and the executable checker

This module maps the parsed `CON` and `DER` records directly to the sensed
constraint representation used by the verified checker. VIPR indices match the
pool indices because equality rows remain single sensed rows.
-/

namespace ViprCheck.Pipeline

open ViprCheck.Cert ViprCheck.Ast

/-- The sensed constraint rows of the certificate, with objective references resolved. -/
def conSLes (v : Vipr) : List SLe :=
  v.cons.toList.map (fun c => ⟨c.sense, c.resolvedForm v.objTerms, c.rhs⟩)

/-- Resolve a derivation's stated form, substituting the objective when requested. -/
def derForm (v : Vipr) (d : ViprDer) : LinForm :=
  if d.usesObj then v.objTerms.map (fun q => (⟨q.1, q.2⟩ : Term)) else d.form

/-- Interpret one parsed derivation as a sensed checker step. -/
def derToSStep (v : Vipr) (d : ViprDer) : SStep :=
  { stated := ⟨d.sense, derForm v d, d.rhs⟩
    reason := match d.reason with
      | .asm => .asm
      | .lin terms => .lin (terms.map (fun p => (p.2, p.1)))
      | .rnd terms => .rnd (terms.map (fun p => (p.2, p.1)))
      | .uns i1 l1 i2 l2 => .uns i1 l1 i2 l2
      | .sol => .sol }

def viprSteps (v : Vipr) : List SStep :=
  v.ders.toList.map (derToSStep v)

/-- Full-semantics checker for infeasibility certificates. -/
def checkSem (v : Vipr) : Bool :=
  checkSemCore v.intVars (conSLes v) (viprSteps v)

/-- Acceptance proves infeasibility of the certificate's own sensed `CON` rows. -/
theorem checkSem_sound (v : Vipr) (h : checkSem v = true) :
    ∀ a, (∀ j ∈ v.intVars, IsIntVal (a j)) →
      (∀ c ∈ conSLes v, SLe.sat c a) → False :=
  checkSemCore_sound v.intVars (conSLes v) (viprSteps v) h

/-- A checked refutation of a row subset also refutes the original system. -/
theorem checkSem_subset_sound (original sliced : Vipr)
    (hint : sliced.intVars = original.intVars)
    (hrows : ∀ c ∈ conSLes sliced, c ∈ conSLes original)
    (hcheck : checkSem sliced = true) :
    ∀ a, (∀ j ∈ original.intVars, IsIntVal (a j)) →
      (∀ c ∈ conSLes original, SLe.sat c a) → False := by
  intro a hintOriginal hrowsOriginal
  apply checkSem_sound sliced hcheck a
  · intro j hj
    apply hintOriginal j
    simpa [hint] using hj
  · intro c hc
    exact hrowsOriginal c (hrows c hc)

end ViprCheck.Pipeline
