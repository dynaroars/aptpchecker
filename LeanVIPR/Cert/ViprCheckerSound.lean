import LeanVIPR.Cert.ViprChecker

/-!
# Soundness of the array-backed VIPR checker

This module proves the production checker sound directly against the declarative
VIPR proof system. No second executable checker or executable-checker equivalence
theorem is involved.
-/

namespace LeanVIPR.Cert.ViprChecker

open LeanVIPR.Ast LeanVIPR.Cert LeanVIPR.Pipeline
open LeanVIPR.Ast.Vipr LeanVIPR.Cert.ViprSystem

theorem poolEntry_eq (pool : CheckerPool) (i : Nat) :
    poolEntry pool i = pool.toList.getD i sdflt := by
  simp [poolEntry, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem poolRow_eq (pool : CheckerPool) (i : Nat) :
    poolRow pool i = spoolRow pool.toList i := by
  simp [poolRow, spoolRow, poolEntry_eq]

theorem poolAsm_eq (pool : CheckerPool) (i : Nat) :
    poolAsm pool i = spoolAsm pool.toList i := by
  simp [poolAsm, spoolAsm, poolEntry_eq]

theorem resolveRefs_eq (pool : CheckerPool) (comb : List (ℚ × Nat)) :
    resolveRefs pool comb = resolve pool.toList comb := by
  simp [resolveRefs, resolve, poolRow_eq]

theorem collectReferencedAsms_eq (pool : CheckerPool) (comb : List (ℚ × Nat)) :
    collectReferencedAsms pool comb = collectAsms pool.toList comb := by
  induction comb with
  | nil => rfl
  | cons p ps ih => simp [collectReferencedAsms, collectAsms, poolAsm_eq, ih]

theorem entryOf_eq (pool : CheckerPool) (s : SStep) :
    entryOf pool s = sentryOf pool.toList s := by
  cases s with
  | mk stated reason =>
    cases reason <;> simp [entryOf, sentryOf, poolRow_eq, poolAsm_eq,
      collectReferencedAsms_eq]

theorem checkLin_eq (stated : SLe) (cs : List (ℚ × SLe)) :
    checkLin stated cs = linCheck stated cs := rfl

theorem checkRnd_eq (intVars : List Nat) (stated : SLe) (cs : List (ℚ × SLe)) :
    checkRnd intVars stated cs = rndCheck intVars stated cs := rfl

theorem back?_toList (pool : CheckerPool) :
    pool.back? = pool.toList.getLast? := by
  rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?]
  simp [Array.getElem?_toList]

theorem referencesPastB_sound {pool : CheckerPool} {r : SReason}
    (h : referencesPastB pool r = true) : ReferencesPast pool.toList r := by
  cases r with
  | asm => trivial
  | lin comb =>
      intro p hp
      simpa using of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | rnd comb =>
      intro p hp
      simpa using of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  | uns i1 l1 i2 l2 =>
      simp only [referencesPastB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨by simpa using h.1.1.1, by simpa using h.1.1.2,
        by simpa using h.1.2, by simpa using h.2⟩
  | sol => trivial

/-- Boolean acceptance of one array-backed step implies declarative step validity. -/
theorem stepValidB_sound {v : Vipr} {pool : CheckerPool} {s : SStep}
    (h : stepValidB v pool s = true) : Vipr.StepValid v pool.toList s := by
  rw [stepValidB, Bool.and_eq_true] at h
  refine ⟨referencesPastB_sound h.1, ?_⟩
  cases hr : s.reason with
  | asm => trivial
  | lin comb =>
      simp only [hr] at h
      apply ViprRule.linCheck_valid_real
      simpa only [resolveRefs_eq, checkLin_eq] using h.2
  | rnd comb =>
      simp only [hr] at h
      apply ViprRule.rndCheck_valid_real
      simpa only [resolveRefs_eq, checkRnd_eq] using h.2
  | uns i1 l1 i2 l2 =>
      simp only [hr, Bool.and_eq_true] at h
      exact ⟨ViprRule.domSLe_valid_real (by simpa [poolRow_eq] using h.2.1.1),
        ViprRule.domSLe_valid_real (by simpa [poolRow_eq] using h.2.1.2),
        ViprRule.unsBoundsB_valid_real (by simpa [poolRow_eq] using h.2.2)⟩
  | sol =>
      simp only [hr] at h
      exact solReasonB_sound h.2

theorem replaySteps_refines (v : Vipr) :
    ∀ (pool : CheckerPool) (steps : List SStep) (final : CheckerPool),
      replaySteps? v pool steps = some final →
      Vipr.DerivationValid v pool.toList steps ∧
        final.toList = sfreplay pool.toList steps := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro final h
      simp only [replaySteps?] at h
      cases h
      exact ⟨trivial, by simp [sfreplay]⟩
  | cons s ss ih =>
      intro final h
      simp only [replaySteps?] at h
      by_cases hs : stepValidB v pool s = true
      · simp only [hs, if_true] at h
        have htail := ih (pool.push (entryOf pool s)) final h
        have htailValid :
            Vipr.DerivationValid
              v (pool.toList ++ [sentryOf pool.toList s]) ss := by
          simpa [entryOf_eq] using htail.1
        refine ⟨⟨stepValidB_sound hs, htailValid⟩, ?_⟩
        simpa [sfreplay, entryOf_eq] using htail.2
      · simp [hs] at h

theorem initialPool_eq (v : Vipr) :
    (initialPool v).toList = sinitPool (conSLes v) := by
  simp [initialPool, sinitPool, conSLes]

theorem replay_refines {v : Vipr} {last? : Option CheckerEntry}
    (h : replay? v = some last?) :
    Vipr.DerivationValid v (sinitPool (conSLes v)) (viprSteps v) ∧
      last? = (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast? := by
  unfold replay? at h
  cases hr : replaySteps? v (initialPool v) (viprSteps v) with
  | none => simp [hr] at h
  | some final =>
      have hrefine :=
        replaySteps_refines v (initialPool v) (viprSteps v) final hr
      simp only [hr, Option.map_some, Option.some.injEq] at h
      refine ⟨?_, ?_⟩
      · simpa [initialPool_eq] using hrefine.1
      · rw [← h, back?_toList, hrefine.2, initialPool_eq]

theorem finalValidB_sound {v : Vipr} {last? : Option CheckerEntry}
    (hlast : last? = (sfreplay (sinitPool (conSLes v)) (viprSteps v)).getLast?)
    (h : finalValidB v last? = true) : FinalValid v := by
  cases hr : v.rtp with
  | infeas =>
      simp only [FinalValid, hr]
      simp only [finalValidB, hr] at h
      cases he : last? with
      | none =>
          rw [he] at h
          simp [closedAbsurdB] at h
      | some e =>
          simp only [he, closedAbsurdB, Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨e, by rw [← hlast, he], h.1,
            ViprRule.absurdB_sound_real h.2⟩
  | range lb ub =>
      simp only [FinalValid, hr]
      simp only [finalValidB, hr] at h
      by_cases hmin : v.objSense = "min"
      · simp only [if_pos hmin] at h ⊢
        cases lb with
        | none => trivial
        | some lower =>
            cases he : last? with
            | none =>
                rw [he] at h
                simp [closedDominatesB] at h
            | some e =>
                simp only [he, closedDominatesB, Bool.and_eq_true,
                  decide_eq_true_eq] at h
                exact ⟨e, by rw [← hlast, he], h.1,
                  ViprRule.domSLe_valid_real h.2⟩
      · by_cases hmax : v.objSense = "max"
        · simp only [if_neg hmin, if_pos hmax] at h ⊢
          cases ub with
          | none => trivial
          | some upper =>
              cases he : last? with
              | none =>
                  rw [he] at h
                  simp [closedDominatesB] at h
              | some e =>
                  simp only [he, closedDominatesB, Bool.and_eq_true,
                    decide_eq_true_eq] at h
                  exact ⟨e, by rw [← hlast, he], h.1,
                    ViprRule.domSLe_valid_real h.2⟩
        · simp [hmin, hmax] at h

/-- The executable checker refines the declarative VIPR proof system. -/
theorem checkVipr_refines {v : Vipr} (h : checkVipr v = true) :
    Vipr.ProofValid v := by
  simp only [checkVipr, Bool.and_eq_true] at h
  cases hr : replay? v with
  | none => simp [hr] at h
  | some last? =>
      have hrefine := replay_refines (v := v) (last? := last?) hr
      exact ⟨solSectionB_sound h.1, hrefine.1,
        finalValidB_sound hrefine.2 (by simpa [hr] using h.2)⟩

/-- Main soundness theorem for the production VIPR checker. -/
theorem checkVipr_sound (v : Vipr) (h : checkVipr v = true) :
    Vipr.ClaimValid v :=
  Vipr.proofSystem_sound v (checkVipr_refines h)

/-- A checked infeasible row subset also refutes the original mixed-integer system. -/
theorem checkViprInfeasibleSubset_sound (original sliced : Vipr)
    (hinfeas : sliced.rtp = .infeas)
    (hint : sliced.intVars = original.intVars)
    (hrows : ∀ c ∈ conSLes sliced, c ∈ conSLes original)
    (hcheck : checkVipr sliced = true) :
    ∀ a, Feasible original a → False := by
  intro a hfeas
  have hsound : ∀ a, Feasible sliced a → False := by
    simpa [Vipr.ClaimValid, hinfeas] using checkVipr_sound sliced hcheck
  apply hsound a
  refine ⟨?_, ?_⟩
  · intro j hj
    apply hfeas.1 j
    simpa [hint] using hj
  · intro c hc
    exact hfeas.2 c (hrows c hc)

end LeanVIPR.Cert.ViprChecker
