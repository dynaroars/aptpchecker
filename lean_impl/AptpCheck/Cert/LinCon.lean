import Mathlib

/-!
# Sparse linear constraints and Farkas over a valuation

The VIPR certificate and the MILP encoding both speak in *sparse* linear
constraints over a shared variable valuation `ℕ → ℚ` (input vars, per-neuron
pre/post vars, binaries, the objective var). This module gives that representation
and the soundness of a Farkas `lin` step to absurdity: a nonnegative combination of
`≤`-rows whose linear part cancels at a point and whose constant is negative rules
out any satisfying valuation.

This is the engine both `Cert/Vipr` (certificate replay) and the per-leaf refutation
(via `Model/Encoding`) invoke. It is the sparse counterpart of
`Cert/LinComb.farkas_infeasible`.
-/

namespace AptpCheck.Cert

/-- A variable valuation (variable id ↦ value). -/
abbrev Valuation := Nat → ℚ

/-- One `coeff · x[idx]` term of a linear form. -/
structure Term where
  idx : Nat
  coeff : ℚ
  deriving Repr, Inhabited, DecidableEq

/-- A sparse linear form `Σ coeff · x[idx]`. -/
abbrev LinForm := List Term

def LinForm.eval (f : LinForm) (a : Valuation) : ℚ :=
  (f.map (fun t => t.coeff * a t.idx)).sum

/-- A `≤` constraint `form ≤ rhs` (ge/eq rows are normalized to this upstream). -/
structure Le where
  form : LinForm
  rhs : ℚ
  deriving Repr, Inhabited, DecidableEq

def Le.sat (c : Le) (a : Valuation) : Prop := c.form.eval a ≤ c.rhs

/-- Pointwise-`≤` implies `≤` on list sums. -/
private theorem list_sum_le {α} (l : List α) (f g : α → ℚ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have h0 : f a ≤ g a := h a (by simp)
      have iht : (t.map f).sum ≤ (t.map g).sum :=
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      linarith

/-- **Farkas `lin` step to absurdity (sparse form).** A combination of `≤`-rows with
nonnegative multipliers `comb = [(y₁,c₁),…]` whose linear part cancels at `a`
(`Σ yᵢ · cᵢ.form(a) = 0`) and whose constant is negative
(`Σ yᵢ · cᵢ.rhs < 0`) cannot have all rows satisfied at `a`. -/
theorem farkas_le (comb : List (ℚ × Le)) (a : Valuation)
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval a)).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0)
    (hsat : ∀ p ∈ comb, Le.sat p.2 a) : False := by
  have hbound : (comb.map (fun p => p.1 * p.2.form.eval a)).sum
              ≤ (comb.map (fun p => p.1 * p.2.rhs)).sum := by
    apply list_sum_le
    intro p hp
    have hs : p.2.form.eval a ≤ p.2.rhs := hsat p hp
    exact mul_le_mul_of_nonneg_left hs (hnn p hp)
  rw [hcancel] at hbound
  linarith

/-- Corollary: if a valuation satisfies every row of a set that admits such a Farkas
combination, we reach a contradiction — i.e. the row set is infeasible. -/
theorem infeasible_of_farkas (rows : List Le) (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb, p.2 ∈ rows)
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (a : Valuation)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval a)).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0)
    (hsat : ∀ c ∈ rows, Le.sat c a) : False :=
  farkas_le comb a hnn hcancel hneg (fun p hp => hsat p.2 (hsub p hp))

/-- **Certificate ⟹ refutation.** Suppose the encoding `rows` are satisfied by the
real trace `a`, and a Farkas combination refutes `rows` together with the negated
property `objRow` (a row `objForm ≤ rhs`). Then the objective form strictly exceeds
its right-hand side at `a`. Instantiated with `objRow.form.eval a = c · net(x)` and
`objRow.rhs = ρ` (from `encoding_overapprox`) this is exactly per-leaf refutation
`c · net(x) > ρ`. -/
theorem refute_of_cert
    (rows : List Le) (objRow : Le) (a : Valuation)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb, p.2 ∈ (objRow :: rows))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval a)).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0)
    (hrows : ∀ c ∈ rows, Le.sat c a) :
    objRow.rhs < objRow.form.eval a := by
  by_contra h
  rw [not_lt] at h
  have hobj : Le.sat objRow a := h
  have hall : ∀ c ∈ (objRow :: rows), Le.sat c a := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hobj
    · exact hrows c hc'
  exact infeasible_of_farkas _ comb hsub hnn a hcancel hneg hall

end AptpCheck.Cert
