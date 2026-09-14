import LeanVIPR.Cert.ViprRuleSound

/-!
# VIPR claim semantics and soundness

This module extends the infeasibility-only development with the semantic objects
needed for `RTP range`, `SOL`, and derived constraints justified by `{ sol }`.
Unlike ordinary derivation rows, a `{ sol }` objective row is guaranteed at an
optimal valuation, not at every feasible valuation.
-/

namespace LeanVIPR.Ast.Vipr

open LeanVIPR.Ast LeanVIPR.Cert LeanVIPR.Cert.ViprSystem
open LeanVIPR.Pipeline

abbrev NamedSolution := String × List (Nat × ℚ)

def objectiveForm (v : Vipr) : LinForm :=
  v.objTerms.map (fun p => (⟨p.1, p.2⟩ : Term))

def sparseValuation : List (Nat × ℚ) → Valuation
  | [], _ => 0
  | (j, q) :: rest, i => if i = j then q else sparseValuation rest i

def solutionValuation (s : NamedSolution) : RealValuation :=
  fun i => (sparseValuation s.2 i : ℝ)

def objectiveQ (v : Vipr) (s : NamedSolution) : ℚ :=
  (objectiveForm v).eval (sparseValuation s.2)

def objectiveReal (v : Vipr) (a : RealValuation) : ℝ :=
  evalReal (objectiveForm v) a

@[simp] theorem evalReal_solution (f : LinForm) (s : NamedSolution) :
    evalReal f (solutionValuation s) = (f.eval (sparseValuation s.2) : ℝ) := by
  induction f with
  | nil => simp [evalReal, LinForm.eval]
  | cons t ts ih =>
      change
        (t.coeff : ℝ) * (sparseValuation s.2 t.idx : ℝ) +
            evalReal ts (solutionValuation s) =
          ((t.coeff * sparseValuation s.2 t.idx +
            LinForm.eval ts (sparseValuation s.2) : ℚ) : ℝ)
      rw [ih]
      push_cast
      ring

@[simp] theorem objectiveReal_solution (v : Vipr) (s : NamedSolution) :
    objectiveReal v (solutionValuation s) = (objectiveQ v s : ℝ) :=
  evalReal_solution _ _

def Feasible (v : Vipr) (a : RealValuation) : Prop :=
  (∀ j ∈ v.intVars, IsIntReal (a j)) ∧
  (∀ c ∈ conSLes v, satReal c a)

def IsOptimal (v : Vipr) (a : RealValuation) : Prop :=
  Feasible v a ∧
  if v.objSense = "min" then
    ∀ b, Feasible v b → objectiveReal v a ≤ objectiveReal v b
  else if v.objSense = "max" then
    ∀ b, Feasible v b → objectiveReal v b ≤ objectiveReal v a
  else False

def AllSolutionsValid (v : Vipr) : Prop :=
  ∀ s ∈ v.sols.toList, Feasible v (solutionValuation s)

def SolSectionValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => v.sols.toList = []
  | .range lb ub =>
      AllSolutionsValid v ∧
      if v.objSense = "min" then
        match ub with
        | none => True
        | some upper => ∃ s ∈ v.sols.toList, objectiveQ v s ≤ upper
      else if v.objSense = "max" then
        match lb with
        | none => True
        | some lower => ∃ s ∈ v.sols.toList, lower ≤ objectiveQ v s
      else False

def SolReasonValid (v : Vipr) (stated : SLe) : Prop :=
  if v.objSense = "min" then
    ∃ s ∈ v.sols.toList,
      Dominates ⟨'L', objectiveForm v, objectiveQ v s⟩ stated
  else if v.objSense = "max" then
    ∃ s ∈ v.sols.toList,
      Dominates ⟨'G', objectiveForm v, objectiveQ v s⟩ stated
  else False

def Candidate (v : Vipr) (a : RealValuation) : Prop :=
  match v.rtp with
  | .infeas => Feasible v a
  | .range _ _ => IsOptimal v a

theorem candidate_feasible {v : Vipr} {a : RealValuation} (h : Candidate v a) :
    Feasible v a := by
  cases hr : v.rtp with
  | infeas => simpa [Candidate, hr] using h
  | range lb ub =>
      exact (show IsOptimal v a from by simpa [Candidate, hr] using h).1

/-- Soundness of a `{ sol }` derivation row.  For infeasibility certificates the
solution set is empty, so this rule cannot be valid.  For range certificates it
holds at every optimal valuation by comparison with the referenced feasible
solution. -/
theorem solReason_sound {v : Vipr} {stated : SLe} {a : RealValuation}
    (hsols : SolSectionValid v) (hcand : Candidate v a)
    (hreason : SolReasonValid v stated) : satReal stated a := by
  cases hr : v.rtp with
  | infeas =>
      have hempty : v.sols.toList = [] := by
        simpa [SolSectionValid, hr] using hsols
      simp only [SolReasonValid] at hreason
      split_ifs at hreason with hmin hmax
      · obtain ⟨s, hs, _⟩ := hreason
        rw [hempty] at hs
        simp at hs
      · obtain ⟨s, hs, _⟩ := hreason
        rw [hempty] at hs
        simp at hs
  | range lb ub =>
      have hall : AllSolutionsValid v :=
        (show AllSolutionsValid v ∧ _ from by
          simpa [SolSectionValid, hr] using hsols).1
      have hopt : IsOptimal v a := by
        simpa [Candidate, hr] using hcand
      simp only [SolReasonValid] at hreason
      split_ifs at hreason with hmin hmax
      · obtain ⟨s, hs, hdom⟩ := hreason
        have ho := hopt
        simp [IsOptimal, hmin] at ho
        have hle := ho.2 (solutionValuation s) (hall s hs)
        exact dominates_sound hdom (by
          simpa [satReal, objectiveReal, objectiveQ] using hle)
      · obtain ⟨s, hs, hdom⟩ := hreason
        have ho := hopt
        simp [IsOptimal, hmax] at ho
        have hge := ho.2 (solutionValuation s) (hall s hs)
        exact dominates_sound hdom (by
          simpa [satReal, objectiveReal, objectiveQ] using hge)

/-! ## Declarative VIPR proof system -/

def objectiveLowerRow (v : Vipr) (lower : ℚ) : SLe :=
  ⟨'G', objectiveForm v, lower⟩

def objectiveUpperRow (v : Vipr) (upper : ℚ) : SLe :=
  ⟨'L', objectiveForm v, upper⟩

/-- Declarative validity of one VIPR step, including objective rows justified
by `{ sol }`. -/
def StepValid (v : Vipr) (pool : SPool) (s : SStep) : Prop :=
  ReferencesPast pool s.reason ∧
  match s.reason with
  | .asm => True
  | .lin comb => LinValid s.stated (resolve pool comb)
  | .rnd comb => RndValid v.intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      Dominates (spoolRow pool i1) s.stated ∧
      Dominates (spoolRow pool i2) s.stated ∧
      ComplementaryBounds v.intVars (spoolRow pool l1) (spoolRow pool l2)
  | .sol => SolReasonValid v s.stated

def DerivationValid (v : Vipr) (pool : SPool) : List SStep → Prop
  | [] => True
  | s :: ss =>
      StepValid v pool s ∧
      DerivationValid v (pool ++ [sentryOf pool s]) ss

def EndsInClosedAbsurdity (v : Vipr) : Prop :=
  ∃ e,
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e ∧
    e.2 = ∅ ∧ Absurd e.1

def EndsInClosedDominatingRow (v : Vipr) (target : SLe) : Prop :=
  ∃ e,
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e ∧
    e.2 = ∅ ∧ Dominates e.1 target

/-- The final-row condition depends on the relation to prove and objective
direction.  A minimization lower bound and a maximization upper bound need a
closed derived row; the opposite bound is witnessed by `SOL`. -/
def FinalValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => EndsInClosedAbsurdity v
  | .range lb ub =>
      if v.objSense = "min" then
        match lb with
        | none => True
        | some lower => EndsInClosedDominatingRow v (objectiveLowerRow v lower)
      else if v.objSense = "max" then
        match ub with
        | none => True
        | some upper => EndsInClosedDominatingRow v (objectiveUpperRow v upper)
      else False

def ProofValid (v : Vipr) : Prop :=
  SolSectionValid v ∧
  DerivationValid v (sinitPool (conSLes v)) (viprSteps v) ∧
  FinalValid v

def WithinRange (lb ub : Option ℚ) (q : ℝ) : Prop :=
  (match lb with
   | none => True
   | some lower => (lower : ℝ) ≤ q) ∧
  (match ub with
   | none => True
   | some upper => q ≤ (upper : ℝ))

/-- Semantic validity of the result claimed by a VIPR certificate. For `RTP infeas`, no feasible
mixed-integer valuation exists.  For `RTP range`, every listed solution is valid,
the required primal witness exists, and every optimal valuation lies in the
reported interval. -/
def ClaimValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => ∀ a, Feasible v a → False
  | .range lb ub =>
      SolSectionValid v ∧
      ∀ a, IsOptimal v a → WithinRange lb ub (objectiveReal v a)

/-- Every entry produced by a declaratively valid full-result replay is sound at
the relevant candidate valuations: feasible valuations for infeasibility results,
and optimal valuations for range results. -/
theorem replay_sound (v : Vipr) (a : RealValuation)
    (hsols : SolSectionValid v) (hcand : Candidate v a) :
    ∀ (pool : SPool) (steps : List SStep),
      DerivationValid v pool steps →
      (∀ e ∈ pool, EntryHolds (conSLes v) a e) →
      ∀ e ∈ sfreplay pool steps, EntryHolds (conSLes v) a e := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro _ hpool
      simpa [sfreplay] using hpool
  | cons s ss ih =>
      intro hv hpool
      obtain ⟨hstep, hrest⟩ := hv
      refine ih (pool ++ [sentryOf pool s]) hrest ?_
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hpool e he
      · rw [List.mem_singleton.mp he]
        obtain ⟨_, hrule⟩ := hstep
        cases hr : s.reason with
        | asm =>
            simp only [sentryOf, hr]
            intro _ hS
            exact hS s.stated (by simp)
        | lin comb =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro hbase hS
            refine linValid_sound hrule (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact ViprSystem.spoolRow_holds (conSLes v) a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | rnd comb =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro hbase hS
            refine rndValid_sound hrule (candidate_feasible hcand).1 (fun p hp => ?_)
            simp only [resolve, List.mem_map] at hp
            obtain ⟨q, hq, rfl⟩ := hp
            exact ViprSystem.spoolRow_holds (conSLes v) a pool hpool q.2 hbase
              (fun t ht => hS t (mem_collectAsms hq ht))
        | uns i1 l1 i2 l2 =>
            simp only [hr] at hrule
            obtain ⟨hdom1, hdom2, hbnd⟩ := hrule
            simp only [sentryOf, hr]
            intro hbase hS
            rcases complementaryBounds_split hbnd (candidate_feasible hcand).1 with hb1 | hb2
            · refine dominates_sound hdom1 ?_
              refine ViprSystem.spoolRow_holds (conSLes v) a pool hpool i1 hbase
                (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l1
              · rw [hteq]
                exact hb1
              · exact hS t (Finset.mem_union_left _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
            · refine dominates_sound hdom2 ?_
              refine ViprSystem.spoolRow_holds (conSLes v) a pool hpool i2 hbase
                (fun t ht => ?_)
              by_cases hteq : t = spoolRow pool l2
              · rw [hteq]
                exact hb2
              · exact hS t (Finset.mem_union_right _
                  (Finset.mem_erase.mpr ⟨hteq, ht⟩))
        | sol =>
            simp only [hr] at hrule
            simp only [sentryOf, hr]
            intro _ _
            exact solReason_sound hsols hcand hrule

private theorem closedFinal_holds {v : Vipr} {a : RealValuation}
    (hsols : SolSectionValid v) (hcand : Candidate v a)
    (hder : DerivationValid v (sinitPool (conSLes v)) (viprSteps v))
    {e : SLe × SAsm}
    (hlast : (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e)
    (hclosed : e.2 = ∅) : satReal e.1 a := by
  have hall := replay_sound v a hsols hcand
    (sinitPool (conSLes v)) (viprSteps v) hder
    (initialPool_holds (conSLes v) a)
  have he : EntryHolds (conSLes v) a e := hall e (List.mem_of_getLast? hlast)
  exact he (candidate_feasible hcand).2 (by simp [hclosed])

/-- Soundness of the full declarative VIPR proof system, including `SOL`,
`{ sol }`, infeasibility results, and finite objective ranges. -/
theorem proofSystem_sound (v : Vipr)
    (hvalid : ProofValid v) : ClaimValid v := by
  obtain ⟨hsols, hder, hfinal⟩ := hvalid
  cases hr : v.rtp with
  | infeas =>
      rw [ClaimValid, hr]
      intro a hfeas
      have hcand : Candidate v a := by
        simpa [Candidate, hr] using hfeas
      obtain ⟨e, hlast, hclosed, habs⟩ := by
        simpa only [FinalValid, hr] using hfinal
      exact ViprSystem.absurd_unsat habs a
        (closedFinal_holds hsols hcand hder hlast hclosed)
  | range lb ub =>
      rw [ClaimValid, hr]
      refine ⟨hsols, ?_⟩
      intro a hopt
      have hcand : Candidate v a := by
        simpa [Candidate, hr] using hopt
      by_cases hmin : v.objSense = "min"
      · have hsolData := hsols
        simp only [SolSectionValid, hr, if_pos hmin] at hsolData
        have hfinalData := hfinal
        simp only [FinalValid, hr, if_pos hmin] at hfinalData
        have hoptData :
            Feasible v a ∧
            ∀ b, Feasible v b → objectiveReal v a ≤ objectiveReal v b := by
          simpa [IsOptimal, hmin] using hopt
        constructor
        · cases lb with
          | none => trivial
          | some lower =>
              obtain ⟨e, hlast, hclosed, hdom⟩ := by
                simpa only using hfinalData
              have hgoal := ViprSystem.dominates_sound hdom
                (closedFinal_holds hsols hcand hder hlast hclosed)
              simpa [objectiveLowerRow, satReal, objectiveReal] using hgoal
        · cases ub with
          | none => trivial
          | some upper =>
              obtain ⟨s, hs, hupper⟩ := hsolData.2
              have hle := hoptData.2 (solutionValuation s) (hsolData.1 s hs)
              have hupperReal :
                  objectiveReal v (solutionValuation s) ≤ (upper : ℝ) := by
                rw [objectiveReal_solution]
                exact_mod_cast hupper
              exact hle.trans hupperReal
      · by_cases hmax : v.objSense = "max"
        · have hsolData := hsols
          simp only [SolSectionValid, hr, if_neg hmin, if_pos hmax] at hsolData
          have hfinalData := hfinal
          simp only [FinalValid, hr, if_neg hmin, if_pos hmax] at hfinalData
          have hoptData :
              Feasible v a ∧
              ∀ b, Feasible v b → objectiveReal v b ≤ objectiveReal v a := by
            simpa [IsOptimal, hmin, hmax] using hopt
          constructor
          · cases lb with
            | none => trivial
            | some lower =>
                obtain ⟨s, hs, hlower⟩ := hsolData.2
                have hle := hoptData.2 (solutionValuation s) (hsolData.1 s hs)
                have hlowerReal :
                    (lower : ℝ) ≤ objectiveReal v (solutionValuation s) := by
                  rw [objectiveReal_solution]
                  exact_mod_cast hlower
                exact hlowerReal.trans hle
          · cases ub with
            | none => trivial
            | some upper =>
                obtain ⟨e, hlast, hclosed, hdom⟩ := by
                  simpa only using hfinalData
                have hgoal := ViprSystem.dominates_sound hdom
                  (closedFinal_holds hsols hcand hder hlast hclosed)
                simpa [objectiveUpperRow, satReal, objectiveReal] using hgoal
        · simp [SolSectionValid, hr, hmin, hmax] at hsols

/-! ## Executable predicates used by the checker -/

/-- Exact rational satisfaction test used for `SOL` vectors. -/
def satQB (c : SLe) (a : Valuation) : Bool :=
  if c.sense = 'L' then decide (c.form.eval a ≤ c.rhs)
  else if c.sense = 'G' then decide (c.rhs ≤ c.form.eval a)
  else if c.sense = 'E' then decide (c.form.eval a = c.rhs)
  else false

def solutionFeasibleB (v : Vipr) (s : NamedSolution) : Bool :=
  v.intVars.all (fun j => isIntValB (sparseValuation s.2 j)) &&
  (conSLes v).all (fun c => satQB c (sparseValuation s.2))

def allSolutionsB (v : Vipr) : Bool :=
  v.sols.toList.all (solutionFeasibleB v)

def solSectionB (v : Vipr) : Bool :=
  match v.rtp with
  | .infeas => v.sols.toList.isEmpty
  | .range lb ub =>
      allSolutionsB v &&
      if v.objSense = "min" then
        match ub with
        | none => true
        | some upper =>
            v.sols.toList.any (fun s => decide (objectiveQ v s ≤ upper))
      else if v.objSense = "max" then
        match lb with
        | none => true
        | some lower =>
            v.sols.toList.any (fun s => decide (lower ≤ objectiveQ v s))
      else false

def solReasonB (v : Vipr) (stated : SLe) : Bool :=
  if v.objSense = "min" then
    v.sols.toList.any (fun s =>
      domSLe ⟨'L', objectiveForm v, objectiveQ v s⟩ stated)
  else if v.objSense = "max" then
    v.sols.toList.any (fun s =>
      domSLe ⟨'G', objectiveForm v, objectiveQ v s⟩ stated)
  else false

/-! ### Refinement of executable solution checks to the declarative proof system -/

theorem satQB_sound_solution {c : SLe} {s : NamedSolution}
    (h : satQB c (sparseValuation s.2) = true) :
    satReal c (solutionValuation s) := by
  simp only [satQB] at h
  simp only [satReal]
  split_ifs at h ⊢ with hL hG hE
  · rw [evalReal_solution]
    exact_mod_cast of_decide_eq_true h
  · rw [evalReal_solution]
    exact_mod_cast of_decide_eq_true h
  · rw [evalReal_solution]
    exact_mod_cast of_decide_eq_true h

theorem solutionFeasibleB_sound {v : Vipr} {s : NamedSolution}
    (h : solutionFeasibleB v s = true) : Feasible v (solutionValuation s) := by
  rw [solutionFeasibleB, Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro j hj
    have hjb := (List.all_eq_true.mp h.1) j hj
    obtain ⟨z, hz⟩ := isIntValB_sound hjb
    refine ⟨z, ?_⟩
    change (sparseValuation s.2 j : ℝ) = (z : ℝ)
    exact_mod_cast hz
  · intro c hc
    exact satQB_sound_solution ((List.all_eq_true.mp h.2) c hc)

theorem allSolutionsB_sound {v : Vipr} (h : allSolutionsB v = true) :
    AllSolutionsValid v := by
  intro s hs
  exact solutionFeasibleB_sound ((List.all_eq_true.mp h) s hs)

theorem solSectionB_sound {v : Vipr} (h : solSectionB v = true) :
    SolSectionValid v := by
  cases hr : v.rtp with
  | infeas =>
      rw [SolSectionValid, hr]
      change v.sols.toList = []
      cases hs : v.sols.toList with
      | nil => rfl
      | cons s ss =>
          simp [solSectionB, hr, hs] at h
  | range lb ub =>
      rw [SolSectionValid, hr]
      simp only [solSectionB, hr, Bool.and_eq_true] at h
      refine ⟨allSolutionsB_sound h.1, ?_⟩
      by_cases hmin : v.objSense = "min"
      · simp only [if_pos hmin] at h
        simp only [hmin]
        cases ub with
        | none => trivial
        | some upper =>
            obtain ⟨s, hs, hle⟩ := List.any_eq_true.mp h.2
            exact ⟨s, hs, of_decide_eq_true hle⟩
      · by_cases hmax : v.objSense = "max"
        · simp only [if_neg hmin, if_pos hmax] at h
          simp only [hmax]
          cases lb with
          | none => trivial
          | some lower =>
              obtain ⟨s, hs, hle⟩ := List.any_eq_true.mp h.2
              exact ⟨s, hs, of_decide_eq_true hle⟩
        · simp [hmin, hmax] at h

theorem solReasonB_sound {v : Vipr} {stated : SLe}
    (h : solReasonB v stated = true) : SolReasonValid v stated := by
  unfold solReasonB at h
  unfold SolReasonValid
  by_cases hmin : v.objSense = "min"
  · simp only [if_pos hmin] at h ⊢
    obtain ⟨s, hs, hdom⟩ := List.any_eq_true.mp h
    exact ⟨s, hs, ViprRule.domSLe_valid_real hdom⟩
  · by_cases hmax : v.objSense = "max"
    · simp only [if_neg hmin, if_pos hmax] at h ⊢
      obtain ⟨s, hs, hdom⟩ := List.any_eq_true.mp h
      exact ⟨s, hs, ViprRule.domSLe_valid_real hdom⟩
    · simp [hmin, hmax] at h

end LeanVIPR.Ast.Vipr
