import AptpCheck.Cert.LinCon
import AptpCheck.Model.Encoding

/-!
# End-to-end refutation for an affine region (the LP-only / complete-pattern case)

On a leaf that fixes every ReLU sign (a *complete* activation pattern), the network
is affine on the region and the per-leaf MILP is a pure LP. This module closes that
case end to end and kernel-checks it: given the input box and a Farkas certificate
refuting `box ∧ {objForm ≤ ρ}`, the objective strictly exceeds `ρ` on the whole box.
Composing with `fuse_linear` gives per-leaf refutation `c·net(x) > ρ` for a terminal
affine layer (`certified_sound_singleLinear`), the smallest complete instance of the
top-level theorem.
-/

namespace AptpCheck.Pipeline

open AptpCheck.Cert AptpCheck.Model

/-- The trace valuation: input variable `j` (id `j`) holds `x j`; other ids are `0`. -/
def val {inD : ℕ} (x : Fin inD → ℚ) : Valuation :=
  fun n => if h : n < inD then x ⟨n, h⟩ else 0

@[simp] lemma val_apply {inD : ℕ} (x : Fin inD → ℚ) (j : Fin inD) :
    val x j.val = x j := by
  unfold val; rw [dif_pos j.isLt]

/-- The objective form `Σ_j D_j · x_j` over the input variables. -/
def objForm {inD : ℕ} (D : Fin inD → ℚ) : LinForm :=
  List.ofFn (fun i : Fin inD => (⟨i.val, D i⟩ : Term))

lemma objForm_eval {inD : ℕ} (D x : Fin inD → ℚ) :
    (objForm D).eval (val x) = ∑ i, D i * x i := by
  simp only [objForm, LinForm.eval, List.map_ofFn, List.sum_ofFn, Function.comp,
    val_apply]

/-- Box constraints as `≤`-rows: `x_j ≤ hi_j` and `-x_j ≤ -lo_j` for each input. -/
def boxRows {inD : ℕ} (lo hi : Fin inD → ℚ) : List Le :=
  (List.ofFn (fun j : Fin inD => (⟨[⟨j.val, 1⟩], hi j⟩ : Le))) ++
  (List.ofFn (fun j : Fin inD => (⟨[⟨j.val, -1⟩], -(lo j)⟩ : Le)))

lemma boxRows_sat {inD : ℕ} (lo hi x : Fin inD → ℚ)
    (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j) :
    ∀ c ∈ boxRows lo hi, Le.sat c (val x) := by
  intro c hc
  simp only [boxRows, List.mem_append, List.mem_ofFn] at hc
  rcases hc with ⟨i, hi'⟩ | ⟨i, hi'⟩ <;> subst hi' <;>
    simp only [Le.sat, LinForm.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, one_mul, add_zero, neg_one_mul, val_apply]
  · exact (hx i).2
  · linarith [(hx i).1]

/-- **Affine refutation.** If the box rows admit a Farkas combination together with
the negated objective `objForm D ≤ ρ - K`, then the affine objective `Σ D_j x_j + K`
strictly exceeds `ρ` for every `x` in the box. -/
theorem affine_refuted {inD : ℕ} (D : Fin inD → ℚ) (K rhs : ℚ) (lo hi x : Fin inD → ℚ)
    (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb, p.2 ∈ (Le.mk (objForm D) (rhs - K) :: boxRows lo hi))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval (val x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < (∑ i, D i * x i) + K := by
  have h := refute_of_cert (boxRows lo hi) (Le.mk (objForm D) (rhs - K)) (val x) comb
    hsub hnn hcancel hneg (boxRows_sat lo hi x hx)
  have h2 : rhs - K < ∑ i, D i * x i := by rw [← objForm_eval]; exact h
  linarith

/-- **End-to-end soundness for a terminal affine layer.** A Farkas certificate that
refutes the box together with `(c-fused) ≤ ρ` proves the property `c·net(x) > ρ` on
the whole box, where `net(x) = Wx+b`. This is the smallest complete instance of the
top-level theorem: coverage is trivial (a single empty leaf), and the objective form
is `c` fused into the layer via `fuse_linear`. -/
theorem certified_sound_singleLinear {inD outD : ℕ}
    (W : Fin outD → Fin inD → ℚ) (b c : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb, p.2 ∈
      (Le.mk (objForm (fun j => ∑ i, c i * W i j)) (rhs - ∑ i, c i * b i)
        :: boxRows lo hi))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval (val x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ i, c i * ((∑ j, W i j * x j) + b i) := by
  rw [fuse_linear]
  exact affine_refuted (fun j => ∑ i, c i * W i j) (∑ i, c i * b i) rhs lo hi x hx
    comb hsub hnn hcancel hneg

end AptpCheck.Pipeline
