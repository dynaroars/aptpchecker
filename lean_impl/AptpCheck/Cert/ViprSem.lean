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

/-- The combination is itself an absurdity (identically-zero form, rhs contradicting a
valid sense) — which, per the VIPR spec, dominates *any* stated constraint. -/
def linAbsurd (cs : List (ℚ × SLe)) : Bool :=
  (suitLeB cs && formIsZero (scomb cs).form && decide ((scomb cs).rhs < 0)) ||
  (suitGeB cs && formIsZero (scomb cs).form && decide (0 < (scomb cs).rhs))

theorem linAbsurd_false {cs} (h : linAbsurd cs = true) {a : Valuation}
    (hsat : ∀ p ∈ cs, p.2.sat a) : False := by
  simp only [linAbsurd, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hs, hz⟩, hr⟩ | ⟨⟨hs, hz⟩, hr⟩
  · have hle := scomb_le_sat cs a (suitLeB_sound hs) hsat
    rw [formIsZero_sound _ hz a] at hle; linarith
  · have hge := scomb_ge_sat cs a (suitGeB_sound hs) hsat
    rw [formIsZero_sound _ hz a] at hge; linarith

/-- **`lin` step check.** Accepts either normal rhs-domination or an absurd combination. -/
def linCheck (stated : SLe) (cs : List (ℚ × SLe)) : Bool :=
  linAbsurd cs ||
  (formEq (scomb cs).form stated.form &&
   (if stated.sense = 'L' then suitLeB cs && decide ((scomb cs).rhs ≤ stated.rhs)
    else if stated.sense = 'G' then suitGeB cs && decide (stated.rhs ≤ (scomb cs).rhs)
    else false))

theorem linCheck_sound {stated cs} (h : linCheck stated cs = true) {a : Valuation}
    (hsat : ∀ p ∈ cs, p.2.sat a) : stated.sat a := by
  simp only [linCheck, Bool.or_eq_true] at h
  rcases h with ha | h
  · exact (linAbsurd_false ha hsat).elim
  rw [Bool.and_eq_true] at h
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

/-! ## Domination and complementary integer bounds (for `uns` case-splits) -/

/-- An absurdity (identically-zero form, rhs contradicting the sense). -/
def absurdB (c : SLe) : Bool :=
  formIsZero c.form &&
  (if c.sense = 'L' then decide (c.rhs < 0)
   else if c.sense = 'G' then decide (0 < c.rhs)
   else if c.sense = 'E' then decide (c.rhs ≠ 0)
   else false)

theorem absurd_unsat {c : SLe} (h : absurdB c = true) (a : Valuation) : ¬ c.sat a := by
  simp only [absurdB, Bool.and_eq_true] at h
  obtain ⟨hz, hcase⟩ := h
  have hze := formIsZero_sound _ hz a
  simp only [SLe.sat]
  split_ifs at hcase ⊢ with hL hG hE
  · rw [hze]; rw [decide_eq_true_eq] at hcase; exact not_le.mpr hcase
  · rw [hze]; rw [decide_eq_true_eq] at hcase; exact not_le.mpr hcase
  · rw [hze]; rw [decide_eq_true_eq] at hcase; exact fun hh => hcase hh.symm


/-- `c` dominates `d`: either `c` is an absurdity (which, per the VIPR spec, dominates
any constraint), or the forms are equal as functions and the right-hand side is at least
as strong for `d`'s sense (an `=`-row dominates either inequality direction). -/
def domSLe (c d : SLe) : Bool :=
  absurdB c ||
  (formEq c.form d.form &&
   (if d.sense = 'L' then ((c.sense == 'L') || (c.sense == 'E')) && decide (c.rhs ≤ d.rhs)
    else if d.sense = 'G' then ((c.sense == 'G') || (c.sense == 'E')) && decide (d.rhs ≤ c.rhs)
    else if d.sense = 'E' then (c.sense == 'E') && decide (c.rhs = d.rhs)
    else false))

theorem domSLe_sat {c d : SLe} (h : domSLe c d = true) {a : Valuation}
    (hc : c.sat a) : d.sat a := by
  simp only [domSLe, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with habs | ⟨hform, hrest⟩
  · exact absurd hc (absurd_unsat habs a)
  have hfe := formEq_sound hform a
  simp only [SLe.sat] at hc ⊢
  split_ifs at hrest ⊢ with hdL hdG hdE
  · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq] at hrest
    obtain ⟨hcs, hle⟩ := hrest
    rcases hcs with hcs | hcs <;> simp [hcs] at hc <;> linarith
  · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq] at hrest
    obtain ⟨hcs, hle⟩ := hrest
    rcases hcs with hcs | hcs <;> simp [hcs] at hc <;> linarith
  · rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrest
    obtain ⟨hcs, heq⟩ := hrest
    simp [hcs] at hc
    rw [← hfe, hc, heq]

/-- `b1`,`b2` are complementary integer bounds `f ≤ β` / `f ≥ β+1` (in either order):
same form as functions, integer-valued form over `intVars`, integer `β`. -/
def unsBoundsB (intVars : List Nat) (b1 b2 : SLe) : Bool :=
  ((b1.sense == 'L') && (b2.sense == 'G') && formEq b1.form b2.form
    && formIntB intVars b1.form && isIntValB b1.rhs && decide (b2.rhs = b1.rhs + 1))
  ||
  ((b1.sense == 'G') && (b2.sense == 'L') && formEq b1.form b2.form
    && formIntB intVars b2.form && isIntValB b2.rhs && decide (b1.rhs = b2.rhs + 1))

/-- **Exhaustiveness of the integer split.** At any valuation with the integer variables
integral, one of the two complementary bounds holds. -/
theorem unsBounds_split {intVars : List Nat} {b1 b2 : SLe}
    (h : unsBoundsB intVars b1 b2 = true) {a : Valuation}
    (hint : ∀ j ∈ intVars, IsIntVal (a j)) : b1.sat a ∨ b2.sat a := by
  simp only [unsBoundsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, hfe⟩, hfi⟩, hb⟩, hb2⟩ | ⟨⟨⟨⟨⟨h1, h2⟩, hfe⟩, hfi⟩, hb⟩, hb2⟩
  · obtain ⟨m, hm⟩ := formIntB_sound hfi a hint
    obtain ⟨n, hn⟩ := isIntValB_sound hb
    have hfe' := formEq_sound hfe a
    simp only [SLe.sat, h1, h2]
    norm_num
    by_cases hmn : m ≤ n
    · left; rw [hm, hn]; exact_mod_cast hmn
    · right; rw [hb2, hn, ← hfe', hm]
      have : n + 1 ≤ m := by omega
      push_cast
      exact_mod_cast this
  · obtain ⟨m, hm⟩ := formIntB_sound hfi a hint
    obtain ⟨n, hn⟩ := isIntValB_sound hb
    have hfe' := formEq_sound hfe a
    simp only [SLe.sat, h1, h2]
    norm_num
    by_cases hmn : m ≤ n
    · right; rw [hm, hn]; exact_mod_cast hmn
    · left; rw [hb2, hn, hfe', hm]
      have : n + 1 ≤ m := by omega
      push_cast
      exact_mod_cast this

/-! ## Derivation replay over sensed constraints -/

/-- A derivation step: the stated (sensed) row, and its reason (indices reference the
running pool: base constraints `0..m-1`, then derivations). -/
inductive SReason where
  | asm
  | lin (comb : List (ℚ × Nat))
  | rnd (comb : List (ℚ × Nat))
  | uns (i1 l1 i2 l2 : Nat)

structure SStep where
  stated : SLe
  reason : SReason

abbrev SPool := List (SLe × List SLe)
def sdflt : SLe × List SLe := (⟨'L', [], 0⟩, [])
def spoolRow (pool : SPool) (i : Nat) : SLe := (pool.getD i sdflt).1
def spoolAsm (pool : SPool) (i : Nat) : List SLe := (pool.getD i sdflt).2
def resolve (pool : SPool) (comb : List (ℚ × Nat)) : List (ℚ × SLe) :=
  comb.map (fun p => (p.1, spoolRow pool p.2))

/-- The pool entry a step produces. An `uns` (case-split) entry keeps the stated row and
discharges the two branch bounds: its open assumptions are branch `i1`'s minus bound
`l1`, plus branch `i2`'s minus bound `l2`. -/
def sentryOf (pool : SPool) (s : SStep) : SLe × List SLe :=
  match s.reason with
  | .asm => (s.stated, [s.stated])
  | .lin comb => (s.stated, comb.flatMap (fun p => spoolAsm pool p.2))
  | .rnd comb => (s.stated, comb.flatMap (fun p => spoolAsm pool p.2))
  | .uns i1 l1 i2 l2 =>
      (s.stated, ((spoolAsm pool i1).filter (fun t => !(t == spoolRow pool l1)))
              ++ ((spoolAsm pool i2).filter (fun t => !(t == spoolRow pool l2))))

/-- Decidable step validity. `uns`: both branch rows dominate the stated row, and the
two discharged bounds are complementary integer bounds. -/
def svalidB (intVars : List Nat) (pool : SPool) (s : SStep) : Bool :=
  match s.reason with
  | .asm => true
  | .lin comb => linCheck s.stated (resolve pool comb)
  | .rnd comb => rndCheck intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      domSLe (spoolRow pool i1) s.stated && domSLe (spoolRow pool i2) s.stated
      && unsBoundsB intVars (spoolRow pool l1) (spoolRow pool l2)

/-- `e` holds at `a`: given base rows and `e`'s open assumptions, `e`'s row holds. -/
def sentryHolds (base : List SLe) (a : Valuation) (e : SLe × List SLe) : Prop :=
  (∀ c ∈ base, c.sat a) → (∀ s ∈ e.2, s.sat a) → e.1.sat a

theorem sentryHolds_sdflt (base : List SLe) (a : Valuation) : sentryHolds base a sdflt := by
  intro _ _; show (SLe.mk 'L' [] 0).sat a; simp [SLe.sat, LinForm.eval]

theorem sentryHolds_getD (base : List SLe) (a : Valuation) (pool : SPool)
    (hpool : ∀ e ∈ pool, sentryHolds base a e) (i : Nat) :
    sentryHolds base a (pool.getD i sdflt) := by
  by_cases h : i < pool.length
  · rw [List.getD_eq_getElem pool sdflt h]; exact hpool _ (List.getElem_mem h)
  · rw [List.getD_eq_default pool sdflt (by omega)]; exact sentryHolds_sdflt base a

theorem spoolRow_holds (base : List SLe) (a : Valuation) (pool : SPool)
    (hpool : ∀ e ∈ pool, sentryHolds base a e) (i : Nat)
    (hbase : ∀ c ∈ base, c.sat a) (hasm : ∀ s ∈ spoolAsm pool i, s.sat a) :
    (spoolRow pool i).sat a :=
  sentryHolds_getD base a pool hpool i hbase hasm

def sfreplay (pool : SPool) : List SStep → SPool
  | [] => pool
  | s :: ss => sfreplay (pool ++ [sentryOf pool s]) ss

def sfvalidB (intVars : List Nat) (pool : SPool) : List SStep → Bool
  | [] => true
  | s :: ss => svalidB intVars pool s && sfvalidB intVars (pool ++ [sentryOf pool s]) ss

/-- **Replay soundness.** -/
theorem sfreplay_holds (base : List SLe) (intVars : List Nat) (a : Valuation)
    (hint : ∀ j ∈ intVars, IsIntVal (a j)) :
    ∀ (pool : SPool) (steps : List SStep),
      sfvalidB intVars pool steps = true → (∀ e ∈ pool, sentryHolds base a e) →
      ∀ e ∈ sfreplay pool steps, sentryHolds base a e := by
  intro pool steps
  induction steps generalizing pool with
  | nil => intro _ hpool; simpa [sfreplay] using hpool
  | cons s ss ih =>
      intro hv hpool
      rw [sfvalidB, Bool.and_eq_true] at hv
      refine ih (pool ++ [sentryOf pool s]) hv.2 ?_
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact hpool e h
      · rw [List.mem_singleton.mp h]
        have hstep := hv.1
        cases hr : s.reason with
        | asm =>
            simp only [sentryOf, hr]
            intro _ hS; exact hS s.stated (by simp)
        | lin comb =>
            have hval : linCheck s.stated (resolve pool comb) = true := by
              simp only [svalidB, hr] at hstep; exact hstep
            simp only [sentryOf, hr]
            intro hbase hS
            refine linCheck_sound hval (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact spoolRow_holds base a pool hpool q.2 hbase
              (fun t ht => hS t (List.mem_flatMap.mpr ⟨q, hq, ht⟩))
        | rnd comb =>
            have hval : rndCheck intVars s.stated (resolve pool comb) = true := by
              simp only [svalidB, hr] at hstep; exact hstep
            simp only [sentryOf, hr]
            intro hbase hS
            refine rndCheck_sound hval hint (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact spoolRow_holds base a pool hpool q.2 hbase
              (fun t ht => hS t (List.mem_flatMap.mpr ⟨q, hq, ht⟩))
        | uns i1 l1 i2 l2 =>
            have hval : (domSLe (spoolRow pool i1) s.stated
                && domSLe (spoolRow pool i2) s.stated
                && unsBoundsB intVars (spoolRow pool l1) (spoolRow pool l2)) = true := by
              simp only [svalidB, hr] at hstep; exact hstep
            rw [Bool.and_eq_true, Bool.and_eq_true] at hval
            obtain ⟨⟨hdom1, hdom2⟩, hbnd⟩ := hval
            simp only [sentryOf, hr]
            intro hbase hS
            rcases unsBounds_split hbnd hint with hb1 | hb2
            · refine domSLe_sat hdom1 ?_
              refine spoolRow_holds base a pool hpool i1 hbase (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l1
              · rw [hteq]; exact hb1
              · exact hS t (List.mem_append_left _
                  (List.mem_filter.mpr ⟨ht, by simp [hteq]⟩))
            · refine domSLe_sat hdom2 ?_
              refine spoolRow_holds base a pool hpool i2 hbase (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l2
              · rw [hteq]; exact hb2
              · exact hS t (List.mem_append_right _
                  (List.mem_filter.mpr ⟨ht, by simp [hteq]⟩))

/-! ## Acceptance -/

/-- Initial pool from the base (CON) rows, each with no assumptions. -/
def sinitPool (base : List SLe) : SPool := base.map (fun c => (c, ([] : List SLe)))

theorem sinitPool_holds (base : List SLe) (a : Valuation) :
    ∀ e ∈ sinitPool base, sentryHolds base a e := by
  intro e he
  simp only [sinitPool, List.mem_map] at he
  obtain ⟨c, hc, rfl⟩ := he
  intro hbase _; exact hbase c hc

/-- **Certificate ⟹ infeasibility.** A valid replay ending in an absurdity with no open
assumptions proves the base (CON) rows infeasible over integer-declared variables. -/
theorem sem_infeasible (base : List SLe) (intVars : List Nat) (steps : List SStep)
    (hv : sfvalidB intVars (sinitPool base) steps = true)
    (e : SLe × List SLe) (hmem : e ∈ sfreplay (sinitPool base) steps)
    (hasm : e.2 = []) (habs : absurdB e.1 = true) :
    ∀ a, (∀ j ∈ intVars, IsIntVal (a j)) → (∀ c ∈ base, c.sat a) → False := by
  intro a hint hbase
  have hall := sfreplay_holds base intVars a hint (sinitPool base) steps hv (sinitPool_holds base a)
  have hE : sentryHolds base a e := hall e hmem
  have hsat : e.1.sat a := hE hbase (by rw [hasm]; intro s hs; simp at hs)
  exact absurd_unsat habs a hsat

/-- Runnable checker over an abstract base + step list. -/
def checkSemCore (intVars : List Nat) (base : List SLe) (steps : List SStep) : Bool :=
  sfvalidB intVars (sinitPool base) steps &&
  (match (sfreplay (sinitPool base) steps).getLast? with
   | some e => absurdB e.1 && e.2.isEmpty
   | none => false)

/-- **Soundness of the runnable checker.** -/
theorem checkSemCore_sound (intVars : List Nat) (base : List SLe) (steps : List SStep)
    (h : checkSemCore intVars base steps = true) :
    ∀ a, (∀ j ∈ intVars, IsIntVal (a j)) → (∀ c ∈ base, c.sat a) → False := by
  simp only [checkSemCore, Bool.and_eq_true] at h
  obtain ⟨hv, hacc⟩ := h
  rcases hgl : (sfreplay (sinitPool base) steps).getLast? with _ | e
  · rw [hgl] at hacc; simp at hacc
  · rw [hgl] at hacc; simp only [Bool.and_eq_true] at hacc
    obtain ⟨habs, hemp⟩ := hacc
    have hasm : e.2 = [] := by
      cases hc : e.2 with | nil => rfl | cons x t => rw [hc] at hemp; simp at hemp
    exact sem_infeasible base intVars steps hv e (List.mem_of_getLast? hgl) hasm habs

end AptpCheck.Cert
