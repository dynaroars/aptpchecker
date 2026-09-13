import ViprCheck.Cert.ViprSystemSound
import ViprCheck.Pipeline.Vipr

/-!
# Soundness of the executable VIPR checker over standard MILP semantics

`ViprSystemSound` proves soundness of a declarative VIPR derivation.  This module
proves the separate implementation theorem for the executable Boolean checker:

```text
checkSem v = true
  → the rational rows in v.CON have no real solution
      whose declared integer variables are integral.
```

The proof follows the code that runs: `linCheck`, `rndCheck`, `domSLe`,
`unsBoundsB`, `svalidB`, `sfvalidB`, and `checkSemCore`.  It does not assume
`StepValid`, `DerivationValid`, or `CertificateValid`.
-/

namespace ViprCheck.Cert.ViprChecker

open ViprCheck.Cert ViprCheck.Cert.ViprSystem

/-! ## Boolean arithmetic checks imply their real-semantic counterparts -/

private def evalALReal (al : List (Nat × ℚ)) (a : RealValuation) : ℝ :=
  (al.map (fun p => (p.2 : ℝ) * a p.1)).sum

@[simp] private theorem evalALReal_cons (p : Nat × ℚ) (tl : List (Nat × ℚ))
    (a : RealValuation) :
    evalALReal (p :: tl) a = (p.2 : ℝ) * a p.1 + evalALReal tl a := by
  simp [evalALReal]

private theorem addTerm_eval_real (al : List (Nat × ℚ)) (i : Nat) (c : ℚ)
    (a : RealValuation) :
    evalALReal (addTerm al i c) a = evalALReal al a + (c : ℝ) * a i := by
  induction al with
  | nil => simp [addTerm, evalALReal]
  | cons hd tl ih =>
      obtain ⟨j, d⟩ := hd
      by_cases heq : i = j
      · subst heq
        simp only [addTerm, beq_self_eq_true, if_true, evalALReal_cons]
        push_cast
        ring
      · have hcond : ¬ ((i == j) = true) := by
          rw [beq_iff_eq]
          exact heq
        simp only [addTerm, if_neg hcond, evalALReal_cons, ih]
        ring

private theorem normForm_foldl_eval_real (f : LinForm) (al : List (Nat × ℚ))
    (a : RealValuation) :
    evalALReal (f.foldl (fun acc t => addTerm acc t.idx t.coeff) al) a =
      evalALReal al a + evalReal f a := by
  induction f generalizing al with
  | nil => simp [evalReal]
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih (addTerm al t.idx t.coeff), addTerm_eval_real]
      have hcons :
          evalReal (t :: ts) a = (t.coeff : ℝ) * a t.idx + evalReal ts a := by
        simp [evalReal]
      rw [hcons]
      ring

private theorem normForm_eval_real (f : LinForm) (a : RealValuation) :
    evalALReal (normForm f) a = evalReal f a := by
  have h := normForm_foldl_eval_real f [] a
  simpa [normForm, evalALReal] using h

private theorem evalALReal_zero_of_all (al : List (Nat × ℚ)) (a : RealValuation)
    (h : ∀ p ∈ al, p.2 = 0) : evalALReal al a = 0 := by
  induction al with
  | nil => simp [evalALReal]
  | cons p tl ih =>
      simp only [evalALReal_cons, h p (by simp), Rat.cast_zero, zero_mul,
        ih (fun q hq => h q (by simp [hq])), zero_add]

private theorem formIsZero_sound_real {f : LinForm} (h : formIsZero f = true) :
    FormZeroReal f := by
  intro a
  rw [← normForm_eval_real]
  refine evalALReal_zero_of_all _ a (fun p hp => ?_)
  exact eq_of_beq ((List.all_eq_true.mp h) p hp)

private theorem formEq_sound_real {f g : LinForm} (h : formEq f g = true) :
    FormEqReal f g := by
  intro a
  have hz := formIsZero_sound_real h a
  simp [sNegForm, evalReal_append, evalReal_scale] at hz
  linarith

private theorem evalReal_isInt (f : LinForm) (a : RealValuation)
    (h : ∀ t ∈ f, IsIntVal t.coeff ∧ IsIntReal (a t.idx)) :
    IsIntReal (evalReal f a) := by
  induction f with
  | nil => exact ⟨0, by simp [evalReal]⟩
  | cons t ts ih =>
      obtain ⟨⟨c, hc⟩, ⟨v, hv⟩⟩ := h t (by simp)
      obtain ⟨m, hm⟩ := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
      refine ⟨c * v + m, ?_⟩
      change (t.coeff : ℝ) * a t.idx + evalReal ts a = ((c * v + m : ℤ) : ℝ)
      rw [hc, hv, hm]
      push_cast
      ring

private theorem formIntB_sound_real {intVars : List Nat} {f : LinForm}
    (h : formIntB intVars f = true) : FormIntegralReal intVars f := by
  intro a hint
  apply evalReal_isInt f a
  intro t ht
  have hb := (List.all_eq_true.mp h) t ht
  rw [Bool.and_eq_true] at hb
  exact ⟨isIntValB_sound hb.1, hint t.idx (of_decide_eq_true hb.2)⟩

private theorem senseSign_cast (s : Char) :
    senseSignReal s = ((senseSign s : ℚ) : ℝ) := by
  simp only [senseSignReal, senseSign]
  split_ifs <;> norm_num

private theorem suitLeB_sound_real {cs : List (ℚ × SLe)} (h : suitLeB cs = true) :
    SuitableLe cs := by
  intro p hp
  rw [senseSign_cast]
  exact_mod_cast suitLeB_sound h p hp

private theorem suitGeB_sound_real {cs : List (ℚ × SLe)} (h : suitGeB cs = true) :
    SuitableGe cs := by
  intro p hp
  rw [senseSign_cast]
  exact_mod_cast suitGeB_sound h p hp

private theorem linAbsurd_sound_real {cs : List (ℚ × SLe)}
    (h : linAbsurd cs = true) : LinAbsurd cs := by
  simp only [linAbsurd, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hs, hz⟩, hrhs⟩ | ⟨⟨hs, hz⟩, hrhs⟩
  · exact Or.inl ⟨suitLeB_sound_real hs, formIsZero_sound_real hz, hrhs⟩
  · exact Or.inr ⟨suitGeB_sound_real hs, formIsZero_sound_real hz, hrhs⟩

theorem linCheck_valid_real {stated : SLe} {cs : List (ℚ × SLe)}
    (h : linCheck stated cs = true) : LinValid stated cs := by
  simp only [linCheck, Bool.or_eq_true] at h
  rcases h with habs | hnormal
  · exact Or.inl (linAbsurd_sound_real habs)
  · rw [Bool.and_eq_true] at hnormal
    obtain ⟨hform, hrest⟩ := hnormal
    refine Or.inr ⟨formEq_sound_real hform, ?_⟩
    split_ifs at hrest with hL hG
    · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
      exact Or.inl ⟨hL, suitLeB_sound_real hrest.1, hrest.2⟩
    · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
      exact Or.inr ⟨hG, suitGeB_sound_real hrest.1, hrest.2⟩

theorem rndCheck_valid_real {intVars : List Nat} {stated : SLe}
    {cs : List (ℚ × SLe)} (h : rndCheck intVars stated cs = true) :
    RndValid intVars stated cs := by
  simp only [rndCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hform, hInt⟩, hrest⟩ := h
  refine ⟨formEq_sound_real hform, formIntB_sound_real hInt, ?_⟩
  split_ifs at hrest with hL hG
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    exact Or.inl ⟨hL, suitLeB_sound_real hrest.1, hrest.2⟩
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hrest
    exact Or.inr ⟨hG, suitGeB_sound_real hrest.1, hrest.2⟩

theorem absurdB_sound_real {c : SLe} (h : absurdB c = true) : Absurd c := by
  simp only [absurdB, Bool.and_eq_true] at h
  obtain ⟨hz, hcase⟩ := h
  refine ⟨formIsZero_sound_real hz, ?_⟩
  split_ifs at hcase with hL hG hE
  · rw [decide_eq_true_eq] at hcase
    exact Or.inl ⟨hL, hcase⟩
  · rw [decide_eq_true_eq] at hcase
    exact Or.inr (Or.inl ⟨hG, hcase⟩)
  · rw [decide_eq_true_eq] at hcase
    exact Or.inr (Or.inr ⟨hE, hcase⟩)

theorem domSLe_valid_real {c d : SLe} (h : domSLe c d = true) :
    Dominates c d := by
  simp only [domSLe, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with habs | ⟨hform, hrest⟩
  · exact Or.inl (absurdB_sound_real habs)
  · refine Or.inr ⟨formEq_sound_real hform, ?_⟩
    split_ifs at hrest with hdL hdG hdE
    · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
        decide_eq_true_eq] at hrest
      exact Or.inl ⟨hdL, hrest.1, hrest.2⟩
    · rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
        decide_eq_true_eq] at hrest
      exact Or.inr (Or.inl ⟨hdG, hrest.1, hrest.2⟩)
    · rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrest
      exact Or.inr (Or.inr ⟨hdE, hrest.1, hrest.2⟩)

theorem unsBoundsB_valid_real {intVars : List Nat} {b1 b2 : SLe}
    (h : unsBoundsB intVars b1 b2 = true) : ComplementaryBounds intVars b1 b2 := by
  simp only [unsBoundsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, hform⟩, hInt⟩, hb⟩, hrhs⟩ |
      ⟨⟨⟨⟨⟨h1, h2⟩, hform⟩, hInt⟩, hb⟩, hrhs⟩
  · exact Or.inl ⟨h1, h2, formEq_sound_real hform, formIntB_sound_real hInt,
      isIntValB_sound hb, hrhs⟩
  · exact Or.inr ⟨h1, h2, formEq_sound_real hform, formIntB_sound_real hInt,
      isIntValB_sound hb, hrhs⟩

/-! ## Soundness of the Boolean replay -/

/-- Every pool entry produced by a successful Boolean replay is sound over real
valuations under exactly the open assumptions recorded by the executable checker. -/
theorem sfreplay_holds_real (base : List SLe) (intVars : List Nat)
    (a : RealValuation) (hint : ∀ j ∈ intVars, IsIntReal (a j)) :
    ∀ (pool : SPool) (steps : List SStep),
      sfvalidB intVars pool steps = true →
      (∀ e ∈ pool, EntryHolds base a e) →
      ∀ e ∈ sfreplay pool steps, EntryHolds base a e := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro _ hpool
      simpa [sfreplay] using hpool
  | cons s ss ih =>
      intro hv hpool
      rw [sfvalidB, Bool.and_eq_true] at hv
      refine ih (pool ++ [sentryOf pool s]) hv.2 ?_
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hpool e he
      · rw [List.mem_singleton.mp he]
        have hstep := hv.1
        cases hr : s.reason with
        | asm =>
            simp only [sentryOf, hr]
            intro _ hS
            exact hS s.stated (by simp)
        | lin comb =>
            have hval : linCheck s.stated (resolve pool comb) = true := by
              simp only [svalidB, hr] at hstep
              exact hstep
            simp only [sentryOf, hr]
            intro hbase hS
            refine linValid_sound (linCheck_valid_real hval) (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact ViprSystem.spoolRow_holds base a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | rnd comb =>
            have hval : rndCheck intVars s.stated (resolve pool comb) = true := by
              simp only [svalidB, hr] at hstep
              exact hstep
            simp only [sentryOf, hr]
            intro hbase hS
            refine rndValid_sound (rndCheck_valid_real hval) hint (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact ViprSystem.spoolRow_holds base a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | uns i1 l1 i2 l2 =>
            have hval :
                (domSLe (spoolRow pool i1) s.stated &&
                  domSLe (spoolRow pool i2) s.stated &&
                  unsBoundsB intVars (spoolRow pool l1) (spoolRow pool l2)) = true := by
              simp only [svalidB, hr] at hstep
              exact hstep
            rw [Bool.and_eq_true, Bool.and_eq_true] at hval
            obtain ⟨⟨hdom1, hdom2⟩, hbnd⟩ := hval
            simp only [sentryOf, hr]
            intro hbase hS
            rcases complementaryBounds_split (unsBoundsB_valid_real hbnd) hint with hb1 | hb2
            · refine dominates_sound (domSLe_valid_real hdom1) ?_
              refine ViprSystem.spoolRow_holds base a pool hpool i1 hbase
                (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l1
              · rw [hteq]
                exact hb1
              · exact hS t (Finset.mem_union_left _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
            · refine dominates_sound (domSLe_valid_real hdom2) ?_
              refine ViprSystem.spoolRow_holds base a pool hpool i2 hbase
                (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l2
              · rw [hteq]
                exact hb2
              · exact hS t (Finset.mem_union_right _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
        | sol =>
            simp [svalidB, hr] at hstep

/-- Soundness of the executable replay core for standard mixed-integer semantics:
continuous variables range over `ℝ`, while declared integer variables are integer
casts. -/
theorem checkSemCore_sound_real (intVars : List Nat) (base : List SLe)
    (steps : List SStep) (h : checkSemCore intVars base steps = true) :
    ∀ a : RealValuation,
      (∀ j ∈ intVars, IsIntReal (a j)) →
      (∀ c ∈ base, satReal c a) →
      False := by
  simp only [checkSemCore, Bool.and_eq_true] at h
  obtain ⟨hv, hacc⟩ := h
  rcases hlast : (sfreplay (sinitPool base) steps).getLast? with _ | e
  · rw [hlast] at hacc
    simp at hacc
  · rw [hlast] at hacc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
    obtain ⟨habs, hasm⟩ := hacc
    intro a hint hbase
    have hall := sfreplay_holds_real base intVars a hint (sinitPool base) steps hv
      (ViprSystem.initialPool_holds base a)
    have he : EntryHolds base a e := hall e (List.mem_of_getLast? hlast)
    have hsat : satReal e.1 a := he hbase (by simp [hasm])
    exact ViprSystem.absurd_unsat (absurdB_sound_real habs) a hsat

end ViprCheck.Cert.ViprChecker

namespace ViprCheck.Pipeline

open ViprCheck.Ast
open ViprCheck.Cert.ViprSystem

/-- **Soundness of the executable parsed-certificate checker over standard MILP
semantics.** If `checkSem` accepts, the certificate's rational `CON` rows have no
real solution satisfying the declared integrality conditions. -/
theorem checkSem_sound_real (v : Vipr) (h : checkSem v = true) :
    ∀ a : RealValuation,
      (∀ j ∈ v.intVars, IsIntReal (a j)) →
      (∀ c ∈ conSLes v, satReal c a) →
      False :=
  ViprCheck.Cert.ViprChecker.checkSemCore_sound_real
    v.intVars (conSLes v) (viprSteps v) h

end ViprCheck.Pipeline
