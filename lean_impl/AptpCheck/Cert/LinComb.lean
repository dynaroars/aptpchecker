import Mathlib

/-!
# Farkas certificates (the checking direction)

The only mathematics the leaf checker relies on is the *soundness* (easy)
direction of Farkas' lemma: a nonnegative combination of the rows of `A x ≤ b`
that cancels the variables and leaves a negative constant witnesses that the
system is infeasible. This is the content of a VIPR `lin` derivation whose result
is the absurdity `0 ≤ -1`.

We work over `ℚ` with rows indexed by `Fin m` and columns by `Fin n`, using plain
functions rather than `Matrix` to keep the reduction kernel-cheap.
-/

namespace AptpCheck.Cert

variable {m n : ℕ}

/-- `x` satisfies the rational system `A x ≤ b`. -/
def Sat (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ) : Prop :=
  ∀ i, (∑ j, A i j * x j) ≤ b i

/-- **Farkas, checking direction.** If `y ≥ 0`, `yᵀA = 0`, and `yᵀb < 0`, then the
system `A x ≤ b` has no solution. This is the semantic content of a VIPR `lin`
step deriving `0 ≤ -1`. -/
theorem farkas_infeasible
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (y : Fin m → ℚ)
    (hy : ∀ i, 0 ≤ y i)
    (hyA : ∀ j, (∑ i, y i * A i j) = 0)
    (hyb : (∑ i, y i * b i) < 0) :
    ¬ ∃ x, Sat A b x := by
  rintro ⟨x, hx⟩
  -- yᵀ(Ax) = 0, by cancelling each column.
  have key : (∑ i, y i * (∑ j, A i j * x j)) = 0 := by
    have expand : (∑ i, y i * (∑ j, A i j * x j))
        = ∑ i, ∑ j, y i * A i j * x j := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [expand, Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [← Finset.sum_mul, hyA j, zero_mul]
  -- yᵀ(Ax) ≤ yᵀb, termwise since y ≥ 0 and Ax ≤ b.
  have bound : (∑ i, y i * (∑ j, A i j * x j)) ≤ ∑ i, y i * b i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy i))
  rw [key] at bound
  exact absurd bound (not_le.mpr hyb)

/-- Bundled decidable check: the three Farkas conditions as one proposition. -/
def CheckLin (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (y : Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, (∑ i, y i * A i j) = 0) ∧ (∑ i, y i * b i) < 0

instance (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (y : Fin m → ℚ) :
    Decidable (CheckLin A b y) := by unfold CheckLin; infer_instance

/-- Reflective soundness: passing `CheckLin` proves infeasibility. Evaluated by the
kernel on concrete rationals — no `native_decide`. -/
theorem checkLin_sound {A : Fin m → Fin n → ℚ} {b : Fin m → ℚ} {y : Fin m → ℚ}
    (h : CheckLin A b y) : ¬ ∃ x, Sat A b x :=
  farkas_infeasible A b y h.1 h.2.1 h.2.2

end AptpCheck.Cert
