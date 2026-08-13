import AptpCheck.Cert.Vipr

/-!
# Full VIPR v1.0 verification semantics (sensed constraints)

Real solver certificates use VIPR's *suitable linear combination*: **signed**
multipliers over constraints of mixed senses (`≤`, `≥`, `=`), deriving a row of a
computed sense that must **dominate** the stated one. This module models that
faithfully over *sensed* constraints `SLe`, and proves its soundness by reduction to
per-term monotonicity (the same idea as `lin_sound`, generalized to signed multipliers).

Sign convention (VIPR spec): `s(C) = -1` for `≤`, `+1` for `≥`, `0` for `=`. A
combination with multipliers `λⱼ` derives a `≤` row when every `λⱼ·s(Cⱼ) ≤ 0`, and a
`≥` row when every `λⱼ·s(Cⱼ) ≥ 0`.
-/

namespace AptpCheck.Cert

/-- A sensed linear constraint `form  sense  rhs`, sense ∈ {`'L'` (≤), `'G'` (≥),
`'E'` (=)}. -/
structure SLe where
  sense : Char
  form : LinForm
  rhs : ℚ
deriving Inhabited, DecidableEq

/-- Satisfaction of a sensed constraint (an unrecognized sense is unsatisfiable). -/
def SLe.sat (c : SLe) (a : Valuation) : Prop :=
  if c.sense = 'L' then c.form.eval a ≤ c.rhs
  else if c.sense = 'G' then c.rhs ≤ c.form.eval a
  else if c.sense = 'E' then c.form.eval a = c.rhs
  else False

/-- VIPR sign `s(C)`: `-1` for `≤`, `+1` for `≥`, `0` for `=`. -/
def senseSign (s : Char) : ℚ :=
  if s = 'L' then -1 else if s = 'G' then 1 else 0

/-- Forget the sense (to reuse `combineForm`/`combine`). -/
def SLe.toLe (c : SLe) : Le := ⟨c.form, c.rhs⟩

/-- **Per-term bound (≤ direction).** -/
theorem term_le (lam : ℚ) (c : SLe) (a : Valuation)
    (hsat : c.sat a) (hsuit : lam * senseSign c.sense ≤ 0) :
    lam * c.form.eval a ≤ lam * c.rhs := by
  simp only [SLe.sat, senseSign] at hsat hsuit
  split_ifs at hsat hsuit <;> (try rw [hsat]) <;> nlinarith [hsat, hsuit]

/-- **Per-term bound (≥ direction).** -/
theorem term_ge (lam : ℚ) (c : SLe) (a : Valuation)
    (hsat : c.sat a) (hsuit : 0 ≤ lam * senseSign c.sense) :
    lam * c.rhs ≤ lam * c.form.eval a := by
  simp only [SLe.sat, senseSign] at hsat hsuit
  split_ifs at hsat hsuit <;> (try rw [hsat]) <;> nlinarith [hsat, hsuit]

theorem comb_le_terms (comb : List (ℚ × SLe)) (a : Valuation)
    (hsuit : ∀ p ∈ comb, p.1 * senseSign p.2.sense ≤ 0)
    (hsat : ∀ p ∈ comb, p.2.sat a) :
    (comb.map (fun p => p.1 * p.2.form.eval a)).sum
      ≤ (comb.map (fun p => p.1 * p.2.rhs)).sum := by
  induction comb with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp := term_le p.1 p.2 a (hsat p (by simp)) (hsuit p (by simp))
      have ihp := ih (fun q hq => hsuit q (List.mem_cons.mpr (Or.inr hq)))
                     (fun q hq => hsat q (List.mem_cons.mpr (Or.inr hq)))
      linarith

theorem comb_ge_terms (comb : List (ℚ × SLe)) (a : Valuation)
    (hsuit : ∀ p ∈ comb, 0 ≤ p.1 * senseSign p.2.sense)
    (hsat : ∀ p ∈ comb, p.2.sat a) :
    (comb.map (fun p => p.1 * p.2.rhs)).sum
      ≤ (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  induction comb with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp := term_ge p.1 p.2 a (hsat p (by simp)) (hsuit p (by simp))
      have ihp := ih (fun q hq => hsuit q (List.mem_cons.mpr (Or.inr hq)))
                     (fun q hq => hsat q (List.mem_cons.mpr (Or.inr hq)))
      linarith

/-- The combined form/rhs, reusing `combineForm`/`combine` on sense-forgotten rows. -/
def scomb (comb : List (ℚ × SLe)) : Le := combine (comb.map (fun p => (p.1, p.2.toLe)))

theorem scomb_eval (comb : List (ℚ × SLe)) (a : Valuation) :
    (scomb comb).form.eval a = (comb.map (fun p => p.1 * p.2.form.eval a)).sum := by
  simp only [scomb, combine, eval_combineForm, List.map_map]
  rfl

theorem scomb_rhs (comb : List (ℚ × SLe)) :
    (scomb comb).rhs = (comb.map (fun p => p.1 * p.2.rhs)).sum := by
  simp only [scomb, combine, List.map_map]
  rfl

/-- **Combination row as a `≤` row holds.** -/
theorem scomb_le_sat (comb : List (ℚ × SLe)) (a : Valuation)
    (hsuit : ∀ p ∈ comb, p.1 * senseSign p.2.sense ≤ 0)
    (hsat : ∀ p ∈ comb, p.2.sat a) :
    (scomb comb).form.eval a ≤ (scomb comb).rhs := by
  rw [scomb_eval, scomb_rhs]; exact comb_le_terms comb a hsuit hsat

/-- **Combination row as a `≥` row holds.** -/
theorem scomb_ge_sat (comb : List (ℚ × SLe)) (a : Valuation)
    (hsuit : ∀ p ∈ comb, 0 ≤ p.1 * senseSign p.2.sense)
    (hsat : ∀ p ∈ comb, p.2.sat a) :
    (scomb comb).rhs ≤ (scomb comb).form.eval a := by
  rw [scomb_eval, scomb_rhs]; exact comb_ge_terms comb a hsuit hsat

end AptpCheck.Cert
