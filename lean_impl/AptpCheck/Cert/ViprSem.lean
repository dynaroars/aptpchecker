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

/-! ## Form equality (for constraint domination) -/

/-- Negate a form (as `-1 · f`). -/
def sNegForm (f : LinForm) : LinForm := LinForm.scale (-1) f

theorem sNegForm_eval (f : LinForm) (a : Valuation) : (sNegForm f).eval a = -(f.eval a) := by
  simp [sNegForm, LinForm.eval_scale]

/-- Decidable "the two forms are equal as functions" (their difference is identically 0). -/
def formEq (f g : LinForm) : Bool := formIsZero (f ++ sNegForm g)

theorem formEq_sound {f g : LinForm} (h : formEq f g = true) (a : Valuation) :
    f.eval a = g.eval a := by
  have hz := formIsZero_sound _ h a
  rw [LinForm.eval_append, sNegForm_eval] at hz
  linarith

/-! ## Per-reason checks and soundness -/

/-- Decidable suitability for a `≤`-deriving combination. -/
def suitLeB (cs : List (ℚ × SLe)) : Bool := cs.all (fun p => decide (p.1 * senseSign p.2.sense ≤ 0))
/-- Decidable suitability for a `≥`-deriving combination. -/
def suitGeB (cs : List (ℚ × SLe)) : Bool := cs.all (fun p => decide (0 ≤ p.1 * senseSign p.2.sense))

theorem suitLeB_sound {cs} (h : suitLeB cs = true) : ∀ p ∈ cs, p.1 * senseSign p.2.sense ≤ 0 :=
  fun p hp => of_decide_eq_true ((List.all_eq_true.mp h) p hp)
theorem suitGeB_sound {cs} (h : suitGeB cs = true) : ∀ p ∈ cs, 0 ≤ p.1 * senseSign p.2.sense :=
  fun p hp => of_decide_eq_true ((List.all_eq_true.mp h) p hp)

/-- The stated form is integer-valued (integer coeffs on integer variables). -/
def formIntB (intVars : List Nat) (f : LinForm) : Bool :=
  f.all (fun t => isIntValB t.coeff && decide (t.idx ∈ intVars))

theorem formIntB_sound {intVars f} (h : formIntB intVars f = true) (a : Valuation)
    (hint : ∀ j ∈ intVars, IsIntVal (a j)) : IsIntVal (f.eval a) :=
  LinForm.eval_isInt f a (fun t ht => by
    have hb := (List.all_eq_true.mp h) t ht
    rw [Bool.and_eq_true] at hb
    exact ⟨isIntValB_sound hb.1, hint t.idx (of_decide_eq_true hb.2)⟩)

/-- Rounding up (`≥` direction): an integer-valued `≥ β` implies `≥ ⌈β⌉`. -/
theorem rnd_ge (form : LinForm) (β : ℚ) (a : Valuation)
    (hInt : IsIntVal (form.eval a)) (hsat : β ≤ form.eval a) : ((⌈β⌉ : ℤ) : ℚ) ≤ form.eval a := by
  obtain ⟨n, hn⟩ := hInt
  rw [hn] at hsat ⊢
  exact_mod_cast Int.ceil_le.mpr hsat

/-- **`lin` step check.** -/
def linCheck (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  formEq (scomb cs).form stated.form &&
  (if stated.sense = 'L' then suitLeB cs && decide ((scomb cs).rhs ≤ stated.rhs)
   else if stated.sense = 'G' then suitGeB cs && decide (stated.rhs ≤ (scomb cs).rhs)
   else false)

theorem linCheck_sound {stated cs} (h : linCheck stated cs = true) {a : Valuation}
    (hsat : ∀ p ∈ cs, p.2.sat a) : stated.sat a := by
  simp only [linCheck, Bool.and_eq_true] at h
  obtain ⟨hform, hrest⟩ := h
  have hfe := formEq_sound hform a
  simp only [SLe.sat]
  split_ifs at hrest with hL hG
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    rw [if_pos hL]
    have hle := scomb_le_sat cs a (suitLeB_sound hrest.1) hsat
    rw [← hfe]; linarith [hrest.2]
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    rw [if_neg hL, if_pos hG]
    have hge := scomb_ge_sat cs a (suitGeB_sound hrest.1) hsat
    rw [← hfe]; linarith [hrest.2]

/-- **`rnd` step check.** -/
def rndCheck (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  formEq (scomb cs).form stated.form && formIntB intVars (scomb cs).form &&
  (if stated.sense = 'L' then suitLeB cs && decide (((⌊(scomb cs).rhs⌋ : ℤ) : ℚ) ≤ stated.rhs)
   else if stated.sense = 'G' then suitGeB cs && decide (stated.rhs ≤ ((⌈(scomb cs).rhs⌉ : ℤ) : ℚ))
   else false)

theorem rndCheck_sound {intVars stated cs} (h : rndCheck intVars stated cs = true) {a : Valuation}
    (hint : ∀ j ∈ intVars, IsIntVal (a j)) (hsat : ∀ p ∈ cs, p.2.sat a) : stated.sat a := by
  simp only [rndCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hform, hfi⟩, hrest⟩ := h
  have hfe := formEq_sound hform a
  have hInt := formIntB_sound hfi a hint
  simp only [SLe.sat]
  split_ifs at hrest with hL hG
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    rw [if_pos hL]
    have hle := scomb_le_sat cs a (suitLeB_sound hrest.1) hsat
    have hr := rnd_sound (scomb cs).form (scomb cs).rhs a hInt hle
    rw [← hfe]; simp only [Le.sat] at hr; linarith [hrest.2]
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    rw [if_neg hL, if_pos hG]
    have hge := scomb_ge_sat cs a (suitGeB_sound hrest.1) hsat
    have hr := rnd_ge (scomb cs).form (scomb cs).rhs a hInt hge
    rw [← hfe]; linarith [hrest.2]

end AptpCheck.Cert
