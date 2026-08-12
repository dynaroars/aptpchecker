import Mathlib
import AptpCheck.Model.Network
import AptpCheck.Cert.LinCon

/-!
# Encoding soundness — the two cornerstones

The per-leaf MILP over-approximates the network. Two facts carry that claim:

* `reluBigM_sound` — the exact ReLU relation `v = max t 0`, together with valid
  pre-activation bounds and the natural binary `a = [t ≥ 0]`, satisfies the four
  big-M constraints used by the MILP encoder. So the *real* activation is always a
  feasible point of the relaxed ReLU gadget (feasible set ⊇ real behaviour).

* `affine_interval_sound` — the interval-arithmetic bounds
  `Σ w⁺·lo + w⁻·hi + b ≤ Σ w·x + b ≤ Σ w⁺·hi + w⁻·lo + b` are valid for every `x`
  in the box. This validates the big-M constants and the stability decisions.

These are the ReLU and affine parts of the `encoding_overapprox` theorem (DESIGN §4).
-/

namespace AptpCheck.Model

/-- **Big-M ReLU soundness.** With valid bounds `lb ≤ t ≤ ub`, the exact ReLU value
`v = max t 0` and binary `a = if 0 ≤ t then 1 else 0` satisfy the four big-M
constraints
`v ≤ t - lb·(1-a)`, `t ≤ v`, `v ≤ ub·a`, `0 ≤ v`. -/
theorem reluBigM_sound {lb ub t v a : ℚ}
    (hlb : lb ≤ t) (hub : t ≤ ub)
    (hv : v = max t 0) (ha : a = if 0 ≤ t then (1 : ℚ) else 0) :
    v ≤ t - lb * (1 - a) ∧ t ≤ v ∧ v ≤ ub * a ∧ 0 ≤ v := by
  subst hv ha
  by_cases h : 0 ≤ t
  · rw [if_pos h, max_eq_left h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hlb, hub, h]
  · rw [if_neg h, max_eq_right (le_of_lt (not_le.mp h))]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hlb, hub, not_le.mp h]

/-- **Affine interval soundness.** For any `x` in the box `[lo, hi]`, the exact
interval bounds on an affine combination are valid. `max (w j) 0` is the positive
part `w⁺` and `min (w j) 0` the negative part `w⁻`. -/
theorem affine_interval_sound {n : ℕ} (w x lo hi : Fin n → ℚ) (b : ℚ)
    (hlo : ∀ j, lo j ≤ x j) (hhi : ∀ j, x j ≤ hi j) :
    (∑ j, (max (w j) 0 * lo j + min (w j) 0 * hi j)) + b ≤ (∑ j, w j * x j) + b ∧
    (∑ j, w j * x j) + b ≤ (∑ j, (max (w j) 0 * hi j + min (w j) 0 * lo j)) + b := by
  have hlow : (∑ j, (max (w j) 0 * lo j + min (w j) 0 * hi j)) ≤ (∑ j, w j * x j) := by
    apply Finset.sum_le_sum; intro j _
    have hp : (0 : ℚ) ≤ max (w j) 0 := le_max_right _ _
    have hm : min (w j) 0 ≤ (0 : ℚ) := min_le_right _ _
    have e1 : max (w j) 0 * lo j ≤ max (w j) 0 * x j := mul_le_mul_of_nonneg_left (hlo j) hp
    have e2 : min (w j) 0 * hi j ≤ min (w j) 0 * x j := mul_le_mul_of_nonpos_left (hhi j) hm
    have hsum : max (w j) 0 * x j + min (w j) 0 * x j = w j * x j := by
      rw [← add_mul, max_add_min]; ring
    linarith [e1, e2, hsum]
  have hup : (∑ j, w j * x j) ≤ (∑ j, (max (w j) 0 * hi j + min (w j) 0 * lo j)) := by
    apply Finset.sum_le_sum; intro j _
    have hp : (0 : ℚ) ≤ max (w j) 0 := le_max_right _ _
    have hm : min (w j) 0 ≤ (0 : ℚ) := min_le_right _ _
    have e1 : max (w j) 0 * x j ≤ max (w j) 0 * hi j := mul_le_mul_of_nonneg_left (hhi j) hp
    have e2 : min (w j) 0 * x j ≤ min (w j) 0 * lo j := mul_le_mul_of_nonpos_left (hlo j) hm
    have hsum : max (w j) 0 * x j + min (w j) 0 * x j = w j * x j := by
      rw [← add_mul, max_add_min]; ring
    linarith [e1, e2, hsum]
  exact ⟨by linarith, by linarith⟩

/-- **Stability.** If the lower interval bound is `≥ 0` the neuron is always active
(`max t 0 = t`); if the upper bound is `≤ 0` it is always inactive (`max t 0 = 0`).
Used to justify folding a "stable" neuron soundly. -/
theorem stable_active {lo t : ℚ} (h : 0 ≤ lo) (ht : lo ≤ t) : max t 0 = t :=
  max_eq_left (le_trans h ht)

theorem stable_inactive {hi t : ℚ} (h : hi ≤ 0) (ht : t ≤ hi) : max t 0 = 0 :=
  max_eq_right (le_trans ht h)

/-- **Spec fusion.** Folding the property row `c` into an affine layer:
`c · (Wx+b) = Σ_j (Σ_i c_i W_{ij}) x_j + Σ_i c_i b_i`. The left is the objective on
the network output; the right is a single linear form over the inputs with constant
`Σ_i c_i b_i`. This is the `W_last ← c·W_last` fusion, and gives the objective row of
the per-leaf encoding for the terminal layer. -/
theorem fuse_linear {inD outD : ℕ}
    (W : Fin outD → Fin inD → ℚ) (b c : Fin outD → ℚ) (x : Fin inD → ℚ) :
    (∑ i, c i * ((∑ j, W i j * x j) + b i))
      = (∑ j, (∑ i, c i * W i j) * x j) + (∑ i, c i * b i) := by
  have hsplit : (∑ i, c i * ((∑ j, W i j * x j) + b i))
      = (∑ i, ∑ j, c i * (W i j * x j)) + (∑ i, c i * b i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, Finset.mul_sum]
  rw [hsplit, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

open AptpCheck.Cert in
/-- The four big-M ReLU rows (all normalized to `≤`) for one unstable neuron with
pre-activation variable `preVar`, post-activation `postVar`, and binary `binVar`:
`v ≤ t - lb(1-a)`, `t ≤ v`, `v ≤ ub·a`, `0 ≤ v`. -/
def reluRows (lb ub : ℚ) (preVar postVar binVar : ℕ) : List Le :=
  [ ⟨[⟨postVar, 1⟩, ⟨preVar, -1⟩, ⟨binVar, -lb⟩], -lb⟩,
    ⟨[⟨preVar, 1⟩, ⟨postVar, -1⟩], 0⟩,
    ⟨[⟨postVar, 1⟩, ⟨binVar, -ub⟩], 0⟩,
    ⟨[⟨postVar, -1⟩], 0⟩ ]

open AptpCheck.Cert in
/-- The real activation trace satisfies the big-M ReLU rows: with valid bounds, the
post value `max(pre,0)` and the binary `[pre ≥ 0]` meet all four constraints. This is
`reluBigM_sound` transported to the `Le`/valuation form used by the certificate. -/
theorem reluRows_sat (lb ub : ℚ) (preVar postVar binVar : ℕ) (a : Valuation)
    (hlb : lb ≤ a preVar) (hub : a preVar ≤ ub)
    (hpost : a postVar = max (a preVar) 0)
    (hbin : a binVar = if 0 ≤ a preVar then (1 : ℚ) else 0) :
    ∀ c ∈ reluRows lb ub preVar postVar binVar, Le.sat c a := by
  obtain ⟨c1, c2, c3, c4⟩ := reluBigM_sound hlb hub hpost hbin
  intro c hc
  simp only [reluRows, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] <;>
    nlinarith [c1, c2, c3, c4]

end AptpCheck.Model
