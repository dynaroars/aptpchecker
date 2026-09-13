import ViprCheck.Cert.ViprSystemSound

/-!
# Completeness statements for the VIPR proof system

Soundness starts with a certificate and proves semantic validity.  Completeness
goes in the opposite direction: from semantic infeasibility, construct a finite
certificate.

The full MILP theorem has two mathematically distinct ingredients:

1. exact rational LP infeasibility admits rational Farkas multipliers;
2. mixed-integer infeasibility admits a finite branch-and-cut derivation whose
   leaves are such LP refutations.

The first compilation step is proved below: every explicit rational Farkas
witness is representable by a one-step, closed VIPR certificate.  Consequently,
any rational Farkas completeness theorem immediately yields completeness of the
VIPR LP fragment.  The finite mixed-integer branch-and-cut existence theorem is
named separately rather than silently assumed.
-/

namespace ViprCheck.Cert.ViprCompleteness

open ViprCheck.Cert ViprCheck.Cert.ViprSystem

def SemanticallyInfeasible (base : List SLe) (intVars : List Nat) : Prop :=
  ∀ a : RealValuation,
    (∀ j ∈ intVars, IsIntReal (a j)) →
    (∀ c ∈ base, satReal c a) →
    False

def HasViprRefutation (base : List SLe) (intVars : List Nat) : Prop :=
  ∃ steps : List SStep, CertificateValid intVars base steps

/-- The desired semantic completeness statement for VIPR infeasibility proofs. -/
def ProofSystemComplete : Prop :=
  ∀ (base : List SLe) (intVars : List Nat),
    SemanticallyInfeasible base intVars →
    HasViprRefutation base intVars

/-- An exact rational Farkas witness over the initial VIPR pool.  Multipliers may
be signed because suitability is interpreted using each row's sense. -/
structure RationalFarkasWitness (base : List SLe) where
  comb : List (ℚ × Nat)
  referencesPast : ∀ p ∈ comb, p.2 < base.length
  suitable : SuitableLe (resolve (sinitPool base) comb)
  zero : FormZeroReal (scomb (resolve (sinitPool base) comb)).form
  negative : (scomb (resolve (sinitPool base) comb)).rhs < 0

def RationalFarkasWitness.conclusion {base : List SLe}
    (w : RationalFarkasWitness base) : SLe :=
  ⟨'L', (scomb (resolve (sinitPool base) w.comb)).form,
    (scomb (resolve (sinitPool base) w.comb)).rhs⟩

def RationalFarkasWitness.step {base : List SLe}
    (w : RationalFarkasWitness base) : SStep :=
  ⟨w.conclusion, .lin w.comb⟩

private theorem initial_spoolAsm_eq_empty (base : List SLe) (i : Nat) :
    spoolAsm (sinitPool base) i = ∅ := by
  by_cases hi : i < (sinitPool base).length
  · rw [show spoolAsm (sinitPool base) i =
        ((sinitPool base).getD i sdflt).2 by rfl]
    rw [List.getD_eq_getElem _ _ hi]
    simp [sinitPool]
  · rw [show spoolAsm (sinitPool base) i =
        ((sinitPool base).getD i sdflt).2 by rfl]
    rw [List.getD_eq_default _ _ (by omega)]
    rfl

private theorem witness_assumptions_empty {base : List SLe}
    (w : RationalFarkasWitness base) :
    (sentryOf (sinitPool base) w.step).2 = ∅ := by
  simp only [RationalFarkasWitness.step, sentryOf]
  induction w.comb with
  | nil => rfl
  | cons p ps ih =>
      simp [collectAsms, initial_spoolAsm_eq_empty, ih]

/-- Every exact rational Farkas witness is expressible as a one-step closed VIPR
refutation.  This is the proof-format completeness theorem for LP leaves. -/
theorem farkasWitness_to_vipr {base : List SLe}
    (w : RationalFarkasWitness base) :
    CertificateValid [] base [w.step] := by
  let pool := sinitPool base
  let step := w.step
  refine ⟨?_, ?_⟩
  · refine ⟨?_, trivial⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simpa [sinitPool] using w.referencesPast p hp
    · exact Or.inl (Or.inl ⟨w.suitable, w.zero, w.negative⟩)
  · refine ⟨sentryOf pool step, ?_, ?_, ?_⟩
    · simp [sfreplay, pool, step]
    · simpa [pool, step] using witness_assumptions_empty w
    · refine ⟨?_, Or.inl ⟨rfl, w.negative⟩⟩
      change FormZeroReal w.conclusion.form
      simpa [RationalFarkasWitness.conclusion] using w.zero

/-- Exact rational Farkas completeness, isolated as the mathematical existence
theorem needed by the LP fragment. -/
def RationalFarkasComplete : Prop :=
  ∀ base : List SLe,
    SemanticallyInfeasible base [] →
    Nonempty (RationalFarkasWitness base)

def LPFragmentComplete : Prop :=
  ∀ base : List SLe,
    SemanticallyInfeasible base [] →
    HasViprRefutation base []

/-- If exact rational Farkas multipliers exist for every infeasible rational LP,
then the VIPR proof system is complete for its LP fragment. -/
theorem lpFragment_complete_of_farkas
    (hfarkas : RationalFarkasComplete) : LPFragmentComplete := by
  intro base hinfeas
  obtain ⟨w⟩ := hfarkas base hinfeas
  exact ⟨[w.step], farkasWitness_to_vipr w⟩

/-- Conditional soundness-and-completeness characterization for the rational LP
fragment.  The reverse implication is the already verified VIPR soundness
theorem; the forward implication isolates rational Farkas existence as the only
additional mathematical ingredient. -/
theorem lpFragment_sound_iff_hasProof
    (hfarkas : RationalFarkasComplete) (base : List SLe) :
    SemanticallyInfeasible base [] ↔ HasViprRefutation base [] := by
  constructor
  · exact lpFragment_complete_of_farkas hfarkas base
  · rintro ⟨steps, hcert⟩
    exact proofSystem_sound base [] steps hcert

/-- The remaining theorem needed for full MILP completeness: every semantically
infeasible rational MILP has a finite VIPR derivation.  Keeping this proposition
explicit prevents the cited branch-and-cut completeness result from being
mistaken for something already proved in this development. -/
def FiniteBranchAndCutComplete : Prop := ProofSystemComplete

end ViprCheck.Cert.ViprCompleteness
