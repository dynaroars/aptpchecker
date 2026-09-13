import ViprCheck.Cert.ViprCheckerSound

/-!
# Full VIPR result semantics

This module extends the infeasibility-only development with the semantic objects
needed for `RTP range`, `SOL`, and derived constraints justified by `{ sol }`.
Unlike ordinary derivation rows, a `{ sol }` objective row is guaranteed at an
optimal valuation, not at every feasible valuation.
-/

namespace ViprCheck.Cert.ViprResult

open ViprCheck.Ast ViprCheck.Cert ViprCheck.Cert.ViprSystem
open ViprCheck.Pipeline

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

/-! ## Declarative full-result proof system -/

def objectiveLowerRow (v : Vipr) (lower : ℚ) : SLe :=
  ⟨'G', objectiveForm v, lower⟩

def objectiveUpperRow (v : Vipr) (upper : ℚ) : SLe :=
  ⟨'L', objectiveForm v, upper⟩

/-- Declarative validity of one VIPR result step.  This extends the
infeasibility-only rule relation with the objective row justified by `{ sol }`. -/
def ResultStepValid (v : Vipr) (pool : SPool) (s : SStep) : Prop :=
  ReferencesPast pool s.reason ∧
  match s.reason with
  | .asm => True
  | .lin comb => LinValid s.stated (resolve pool comb)
  | .rnd comb => RndValid v.intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      Dominates (spoolRow pool i1) s.stated ∧
      Dominates (spoolRow pool i2) s.stated ∧
      ComplementaryBounds v.intVars (spoolRow pool l1) (spoolRow pool l2) ∧
      spoolRow pool l1 ∈ spoolAsm pool i1 ∧
      spoolRow pool l2 ∈ spoolAsm pool i2
  | .sol => SolReasonValid v s.stated

def ResultDerivationValid (v : Vipr) (pool : SPool) : List SStep → Prop
  | [] => True
  | s :: ss =>
      ResultStepValid v pool s ∧
      ResultDerivationValid v (pool ++ [sentryOf pool s]) ss

def ClosedAbsurdFinal (v : Vipr) : Prop :=
  ∃ e,
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e ∧
    e.2 = ∅ ∧ Absurd e.1

def ClosedFinalDominates (v : Vipr) (target : SLe) : Prop :=
  ∃ e,
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e ∧
    e.2 = ∅ ∧ Dominates e.1 target

/-- The final-row condition depends on the relation to prove and objective
direction.  A minimization lower bound and a maximization upper bound need a
closed derived row; the opposite bound is witnessed by `SOL`. -/
def FinalResultValid (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => ClosedAbsurdFinal v
  | .range lb ub =>
      if v.objSense = "min" then
        match lb with
        | none => True
        | some lower => ClosedFinalDominates v (objectiveLowerRow v lower)
      else if v.objSense = "max" then
        match ub with
        | none => True
        | some upper => ClosedFinalDominates v (objectiveUpperRow v upper)
      else False

def ResultCertificateValid (v : Vipr) : Prop :=
  SolSectionValid v ∧
  ResultDerivationValid v (sinitPool (conSLes v)) (viprSteps v) ∧
  FinalResultValid v

def WithinRange (lb ub : Option ℚ) (q : ℝ) : Prop :=
  (match lb with
   | none => True
   | some lower => (lower : ℝ) ≤ q) ∧
  (match ub with
   | none => True
   | some upper => q ≤ (upper : ℝ))

/-- Semantic meaning of a checked VIPR result.  For `RTP infeas`, no feasible
mixed-integer valuation exists.  For `RTP range`, every listed solution is valid,
the required primal witness exists, and every optimal valuation lies in the
reported interval. -/
def ResultCorrect (v : Vipr) : Prop :=
  match v.rtp with
  | .infeas => ∀ a, Feasible v a → False
  | .range lb ub =>
      SolSectionValid v ∧
      ∀ a, IsOptimal v a → WithinRange lb ub (objectiveReal v a)

/-- Every entry produced by a declaratively valid full-result replay is sound at
the relevant candidate valuations: feasible valuations for infeasibility results,
and optimal valuations for range results. -/
theorem resultReplay_holds (v : Vipr) (a : RealValuation)
    (hsols : SolSectionValid v) (hcand : Candidate v a) :
    ∀ (pool : SPool) (steps : List SStep),
      ResultDerivationValid v pool steps →
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
            obtain ⟨hdom1, hdom2, hbnd, _, _⟩ := hrule
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
    (hder : ResultDerivationValid v (sinitPool (conSLes v)) (viprSteps v))
    {e : SLe × SAsm}
    (hlast : (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? = some e)
    (hclosed : e.2 = ∅) : satReal e.1 a := by
  have hall := resultReplay_holds v a hsols hcand
    (sinitPool (conSLes v)) (viprSteps v) hder
    (initialPool_holds (conSLes v) a)
  have he : EntryHolds (conSLes v) a e := hall e (List.mem_of_getLast? hlast)
  exact he (candidate_feasible hcand).2 (by simp [hclosed])

/-- Soundness of the full declarative VIPR proof system, including `SOL`,
`{ sol }`, infeasibility results, and finite objective ranges. -/
theorem proofSystem_result_sound (v : Vipr)
    (hvalid : ResultCertificateValid v) : ResultCorrect v := by
  obtain ⟨hsols, hder, hfinal⟩ := hvalid
  cases hr : v.rtp with
  | infeas =>
      rw [ResultCorrect, hr]
      intro a hfeas
      have hcand : Candidate v a := by
        simpa [Candidate, hr] using hfeas
      obtain ⟨e, hlast, hclosed, habs⟩ := by
        simpa only [FinalResultValid, hr] using hfinal
      exact ViprSystem.absurd_unsat habs a
        (closedFinal_holds hsols hcand hder hlast hclosed)
  | range lb ub =>
      rw [ResultCorrect, hr]
      refine ⟨hsols, ?_⟩
      intro a hopt
      have hcand : Candidate v a := by
        simpa [Candidate, hr] using hopt
      by_cases hmin : v.objSense = "min"
      · have hsolData := hsols
        simp only [SolSectionValid, hr, if_pos hmin] at hsolData
        have hfinalData := hfinal
        simp only [FinalResultValid, hr, if_pos hmin] at hfinalData
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
          simp only [FinalResultValid, hr, if_neg hmin, if_pos hmax] at hfinalData
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

/-! ## Executable full-result checker -/

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

def referencesPastB (pool : SPool) : SReason → Bool
  | .asm => true
  | .lin comb => comb.all (fun p => decide (p.2 < pool.length))
  | .rnd comb => comb.all (fun p => decide (p.2 < pool.length))
  | .uns i1 l1 i2 l2 =>
      decide (i1 < pool.length) && decide (l1 < pool.length) &&
      decide (i2 < pool.length) && decide (l2 < pool.length)
  | .sol => true

def resultStepB (v : Vipr) (pool : SPool) (s : SStep) : Bool :=
  referencesPastB pool s.reason &&
  match s.reason with
  | .asm => true
  | .lin comb => linCheck s.stated (resolve pool comb)
  | .rnd comb => rndCheck v.intVars s.stated (resolve pool comb)
  | .uns i1 l1 i2 l2 =>
      domSLe (spoolRow pool i1) s.stated &&
      domSLe (spoolRow pool i2) s.stated &&
      unsBoundsB v.intVars (spoolRow pool l1) (spoolRow pool l2) &&
      decide (spoolRow pool l1 ∈ spoolAsm pool i1) &&
      decide (spoolRow pool l2 ∈ spoolAsm pool i2)
  | .sol => solReasonB v s.stated

def resultDerivationB (v : Vipr) (pool : SPool) : List SStep → Bool
  | [] => true
  | s :: ss =>
      resultStepB v pool s &&
      resultDerivationB v (pool ++ [sentryOf pool s]) ss

def lastClosedAbsurdB (v : Vipr) : Bool :=
  match (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? with
  | none => false
  | some e => decide (e.2 = ∅) && absurdB e.1

def lastClosedDominatesB (v : Vipr) (target : SLe) : Bool :=
  match (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? with
  | none => false
  | some e => decide (e.2 = ∅) && domSLe e.1 target

def finalResultB (v : Vipr) : Bool :=
  match v.rtp with
  | .infeas => lastClosedAbsurdB v
  | .range lb ub =>
      if v.objSense = "min" then
        match lb with
        | none => true
        | some lower => lastClosedDominatesB v (objectiveLowerRow v lower)
      else if v.objSense = "max" then
        match ub with
        | none => true
        | some upper => lastClosedDominatesB v (objectiveUpperRow v upper)
      else false

/-- Runnable checker for both VIPR result kinds. -/
def checkViprResult (v : Vipr) : Bool :=
  solSectionB v &&
  resultDerivationB v (sinitPool (conSLes v)) (viprSteps v) &&
  finalResultB v

/-! ### Refinement of executable checks to the declarative proof system -/

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
    exact ⟨s, hs, ViprChecker.domSLe_valid_real hdom⟩
  · by_cases hmax : v.objSense = "max"
    · simp only [if_neg hmin, if_pos hmax] at h ⊢
      obtain ⟨s, hs, hdom⟩ := List.any_eq_true.mp h
      exact ⟨s, hs, ViprChecker.domSLe_valid_real hdom⟩
    · simp [hmin, hmax] at h

theorem referencesPastB_sound {pool : SPool} {r : SReason}
    (h : referencesPastB pool r = true) : ReferencesPast pool r := by
  cases r with
  | asm => trivial
  | lin comb =>
      intro p hp
      exact of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | rnd comb =>
      intro p hp
      exact of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | uns i1 l1 i2 l2 =>
      simp only [referencesPastB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  | sol => trivial

theorem resultStepB_sound {v : Vipr} {pool : SPool} {s : SStep}
    (h : resultStepB v pool s = true) : ResultStepValid v pool s := by
  rw [resultStepB, Bool.and_eq_true] at h
  refine ⟨referencesPastB_sound h.1, ?_⟩
  cases hr : s.reason with
  | asm => trivial
  | lin comb =>
      simp only [hr] at h
      exact ViprChecker.linCheck_valid_real h.2
  | rnd comb =>
      simp only [hr] at h
      exact ViprChecker.rndCheck_valid_real h.2
  | uns i1 l1 i2 l2 =>
      simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨ViprChecker.domSLe_valid_real h.2.1.1.1.1,
        ViprChecker.domSLe_valid_real h.2.1.1.1.2,
        ViprChecker.unsBoundsB_valid_real h.2.1.1.2,
        h.2.1.2, h.2.2⟩
  | sol =>
      simp only [hr] at h
      exact solReasonB_sound h.2

theorem resultDerivationB_sound (v : Vipr) :
    ∀ (pool : SPool) (steps : List SStep),
      resultDerivationB v pool steps = true →
      ResultDerivationValid v pool steps := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro _
      trivial
  | cons s ss ih =>
      simp only [resultDerivationB, Bool.and_eq_true]
      intro h
      exact ⟨resultStepB_sound h.1, ih _ h.2⟩

theorem finalResultB_sound {v : Vipr} (h : finalResultB v = true) :
    FinalResultValid v := by
  cases hr : v.rtp with
  | infeas =>
      rw [FinalResultValid, hr]
      simp only [finalResultB, hr, lastClosedAbsurdB] at h
      cases hlast :
          (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? with
      | none =>
          rw [hlast] at h
          simp at h
      | some e =>
          rw [hlast, Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨e, hlast, h.1,
            ViprChecker.absurdB_sound_real h.2⟩
  | range lb ub =>
      rw [FinalResultValid, hr]
      simp only [finalResultB, hr] at h
      by_cases hmin : v.objSense = "min"
      · simp only [if_pos hmin] at h ⊢
        cases lb with
        | none => trivial
        | some lower =>
            simp only [lastClosedDominatesB] at h
            cases hlast :
                (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? with
            | none =>
                rw [hlast] at h
                simp at h
            | some e =>
                rw [hlast, Bool.and_eq_true, decide_eq_true_eq] at h
                exact ⟨e, hlast, h.1,
                  ViprChecker.domSLe_valid_real h.2⟩
      · by_cases hmax : v.objSense = "max"
        · simp only [if_neg hmin, if_pos hmax] at h ⊢
          cases ub with
          | none => trivial
          | some upper =>
              simp only [lastClosedDominatesB] at h
              cases hlast :
                  (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? with
              | none =>
                  rw [hlast] at h
                  simp at h
              | some e =>
                  rw [hlast, Bool.and_eq_true, decide_eq_true_eq] at h
                  exact ⟨e, hlast, h.1,
                    ViprChecker.domSLe_valid_real h.2⟩
        · simp [hmin, hmax] at h

/-- The executable Boolean checker refines the declarative full VIPR proof
system. -/
theorem checkViprResult_refines {v : Vipr} (h : checkViprResult v = true) :
    ResultCertificateValid v := by
  simp only [checkViprResult, Bool.and_eq_true] at h
  exact ⟨solSectionB_sound h.1.1,
    resultDerivationB_sound v _ _ h.1.2,
    finalResultB_sound h.2⟩

/-- Main executable-checker soundness theorem for full VIPR results. -/
theorem checkViprResult_sound (v : Vipr) (h : checkViprResult v = true) :
    ResultCorrect v :=
  proofSystem_result_sound v (checkViprResult_refines h)

end ViprCheck.Cert.ViprResult
