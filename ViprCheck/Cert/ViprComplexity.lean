import ViprCheck.Cert.ViprTermination

/-!
# Structural complexity of the VIPR checker

This module gives a source-level cost semantics for the list-based replay used by
`checkViprResult`.  It deliberately does not identify one cost unit with one CPU
instruction:

* `ruleChecks` counts calls to `resultStepB`; the exact cost of a call depends on
  sparse-form sizes and arbitrary-precision rational arithmetic;
* `replaySteps` counts construction of one replay entry;
* `poolCopyCells` counts list cells copied by `pool ++ [entry]`; and
* `assumptionCells` counts open-assumption cells constructed by `sentryOf`;
* `ruleInputCells` counts sparse stated/reference cells presented to rule checks;
  and
* `solutionInputCells` counts the solution-vector cells potentially scanned by
  `RTP range`, `SOL`, and `{ sol }` checks.

The last two fields expose implementation costs hidden by the earlier
one-fuel-per-`DER` termination theorem. Open assumptions are represented as
finite sets. Every such assumption is a row stated by an `asm` derivation, hence
is drawn from the at most `k` rows stated by the certificate's `k` derivation
records. The theorems below prove the resulting quadratic bound on stored and
constructed assumption entries.

The model is a conservative full-run budget.  Rejection may short-circuit before
the budget is consumed, and some `RTP range` results do not need the final replay.
Big-integer bit complexity, finite-set equality-comparison costs, and costs
introduced by the Lean compiler/runtime are outside this source-level model.
-/

namespace ViprCheck.Cert.ViprComplexity

open ViprCheck.Ast ViprCheck.Pipeline
open ViprCheck.Cert
open ViprCheck.Cert.ViprResult
open ViprCheck.Cert.ViprTermination

/-! ## Bounds on finite sets of open assumptions -/

/-- The finite universe of all rows stated by derivation records. It contains
every row that an `asm` record could introduce. -/
def derivationRows (steps : List SStep) : Finset SLe :=
  (steps.map fun s => s.stated).toFinset

theorem stated_mem_derivationRows {s : SStep} {steps : List SStep}
    (hs : s ∈ steps) : s.stated ∈ derivationRows steps := by
  simp only [derivationRows, List.mem_toFinset, List.mem_map]
  exact ⟨s, hs, rfl⟩

theorem derivationRows_card_le (steps : List SStep) :
    (derivationRows steps).card ≤ steps.length := by
  simpa [derivationRows] using
    (List.toFinset_card_le (l := steps.map fun s => s.stated))

/-- Every open-assumption set in a pool is contained in `U`. -/
def AssumptionSubset (U : Finset SLe) (pool : SPool) : Prop :=
  ∀ e ∈ pool, e.2 ⊆ U

theorem spoolAsm_subset {U : Finset SLe} {pool : SPool}
    (hpool : AssumptionSubset U pool) (i : Nat) :
    spoolAsm pool i ⊆ U := by
  by_cases hi : i < pool.length
  · rw [show spoolAsm pool i = (pool.getD i sdflt).2 by rfl]
    rw [List.getD_eq_getElem _ _ hi]
    exact hpool _ (List.getElem_mem hi)
  · rw [show spoolAsm pool i = (pool.getD i sdflt).2 by rfl]
    rw [List.getD_eq_default _ _ (by omega)]
    simp [sdflt]

theorem collectAsms_subset {U : Finset SLe} {pool : SPool}
    (hpool : AssumptionSubset U pool) (comb : List (ℚ × Nat)) :
    collectAsms pool comb ⊆ U := by
  induction comb with
  | nil => simp [collectAsms]
  | cons p ps ih =>
      intro t ht
      simp only [collectAsms, Finset.mem_union] at ht
      rcases ht with ht | ht
      · exact spoolAsm_subset hpool p.2 ht
      · exact ih ht

theorem sentryOf_assumptions_subset {U : Finset SLe}
    {pool : SPool} {s : SStep}
    (hstep : s.reason = .asm → s.stated ∈ U)
    (hpool : AssumptionSubset U pool) :
    (sentryOf pool s).2 ⊆ U := by
  cases hr : s.reason with
  | asm =>
      simpa [sentryOf, hr] using hstep hr
  | lin comb =>
      simpa only [sentryOf, hr] using collectAsms_subset hpool comb
  | rnd comb =>
      simpa only [sentryOf, hr] using collectAsms_subset hpool comb
  | uns i1 l1 i2 l2 =>
      simp only [sentryOf, hr]
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact spoolAsm_subset hpool i1 (Finset.mem_erase.mp ht).2
      · exact spoolAsm_subset hpool i2 (Finset.mem_erase.mp ht).2
  | sol => simp [sentryOf, hr]

theorem assumptionSubset_append_sentry {U : Finset SLe}
    {pool : SPool} {s : SStep}
    (hstep : s.reason = .asm → s.stated ∈ U)
    (hpool : AssumptionSubset U pool) :
    AssumptionSubset U (pool ++ [sentryOf pool s]) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hpool e he
  · rw [List.mem_singleton.mp he]
    exact sentryOf_assumptions_subset hstep hpool

/-- Replay never introduces an assumption outside `U`. -/
theorem sfreplay_assumption_subset (U : Finset SLe) (pool : SPool)
    (steps : List SStep) (hpool : AssumptionSubset U pool)
    (hsteps : ∀ s ∈ steps, s.stated ∈ U) :
    AssumptionSubset U (sfreplay pool steps) := by
  induction steps generalizing pool with
  | nil => simpa [sfreplay] using hpool
  | cons s ss ih =>
      have hs : s.stated ∈ U := hsteps s (by simp)
      have htail : ∀ t ∈ ss, t.stated ∈ U := by
        intro t ht
        exact hsteps t (by simp [ht])
      have hnext := assumptionSubset_append_sentry (fun _ => hs) hpool
      simpa [sfreplay] using
        ih (pool := pool ++ [sentryOf pool s]) hnext htail

theorem sinitPool_assumption_subset (U : Finset SLe) (base : List SLe) :
    AssumptionSubset U (sinitPool base) := by
  intro e he
  simp only [sinitPool, List.mem_map] at he
  obtain ⟨c, _, rfl⟩ := he
  simp

/-- All assumptions in a completed certificate replay are rows stated somewhere
in that certificate. -/
theorem certificate_assumption_subset (v : Vipr) :
    AssumptionSubset (derivationRows (viprSteps v))
      (sfreplay (sinitPool (conSLes v)) (viprSteps v)) := by
  exact sfreplay_assumption_subset _ _ _
    (sinitPool_assumption_subset _ _)
    (fun s hs => stated_mem_derivationRows hs)

/-- Every open-assumption set in a pool has cardinality at most `bound`. -/
def AssumptionBound (bound : Nat) (pool : SPool) : Prop :=
  ∀ e ∈ pool, e.2.card ≤ bound

/-- Every assumption set produced while checking a certificate has cardinality
at most the number `k` of derivation records. -/
theorem certificate_assumption_card_bound (v : Vipr) :
    AssumptionBound (viprSteps v).length
      (sfreplay (sinitPool (conSLes v)) (viprSteps v)) := by
  intro e he
  have hsubset := certificate_assumption_subset v e he
  exact (Finset.card_le_card hsubset).trans (derivationRows_card_le _)

/-- Total number of open-assumption cells resident in a pool. -/
def assumptionCells (pool : SPool) : Nat :=
  (pool.map fun e => e.2.card).sum

theorem assumptionCells_le {bound : Nat} {pool : SPool}
    (hpool : AssumptionBound bound pool) :
    assumptionCells pool ≤ pool.length * bound := by
  induction pool with
  | nil => simp [assumptionCells]
  | cons e es ih =>
      have he := hpool e (by simp)
      have hes : AssumptionBound bound es := by
        intro x hx
        exact hpool x (by simp [hx])
      have hit := ih hes
      change e.2.card + assumptionCells es ≤ (es.length + 1) * bound
      calc
        e.2.card + assumptionCells es ≤ bound + es.length * bound :=
          Nat.add_le_add he hit
        _ = (es.length + 1) * bound := by
          rw [Nat.add_mul]
          omega

/-- Resident open-assumption memory after replay. -/
theorem certificate_assumption_cells_bound (v : Vipr) :
    assumptionCells (sfreplay (sinitPool (conSLes v)) (viprSteps v)) ≤
      ((conSLes v).length + (viprSteps v).length) *
        (viprSteps v).length := by
  have h := assumptionCells_le (certificate_assumption_card_bound v)
  rw [sfreplay_length] at h
  simpa [sinitPool] using h

/-! ## Source-level replay work -/

/-- Number of assumption cells allocated while constructing one replay. -/
def replayAssumptionWork (pool : SPool) : List SStep → Nat
  | [] => 0
  | s :: ss =>
      (sentryOf pool s).2.card +
        replayAssumptionWork (pool ++ [sentryOf pool s]) ss

theorem replayAssumptionWork_le_universe (U : Finset SLe)
    (pool : SPool) (steps : List SStep)
    (hpool : AssumptionSubset U pool)
    (hsteps : ∀ s ∈ steps, s.stated ∈ U) :
    replayAssumptionWork pool steps ≤ steps.length * U.card := by
  induction steps generalizing pool with
  | nil => simp [replayAssumptionWork]
  | cons s ss ih =>
      have hs : s.stated ∈ U := hsteps s (by simp)
      have htail : ∀ t ∈ ss, t.stated ∈ U := by
        intro t ht
        exact hsteps t (by simp [ht])
      have hsub := sentryOf_assumptions_subset (fun _ => hs) hpool
      have hone := Finset.card_le_card hsub
      have hnext := assumptionSubset_append_sentry (fun _ => hs) hpool
      have hrec := ih (pool := pool ++ [sentryOf pool s]) hnext htail
      simp only [replayAssumptionWork, List.length_cons]
      nlinarith

/-- Constructing all finite assumption sets in one replay stores at most `k²`
assumption entries. -/
theorem certificate_replayAssumptionWork_le (v : Vipr) :
    replayAssumptionWork (sinitPool (conSLes v)) (viprSteps v) ≤
      (viprSteps v).length * (viprSteps v).length := by
  have h := replayAssumptionWork_le_universe
    (derivationRows (viprSteps v))
    (sinitPool (conSLes v)) (viprSteps v)
    (sinitPool_assumption_subset _ _)
    (fun s hs => stated_mem_derivationRows hs)
  exact h.trans (Nat.mul_le_mul_left _ (derivationRows_card_le _))

/-- List cells copied by the append `pool ++ [entry]` during one replay. -/
def replayPoolCopyWork (pool : SPool) : List SStep → Nat
  | [] => 0
  | s :: ss =>
      pool.length + replayPoolCopyWork (pool ++ [sentryOf pool s]) ss

/-- The list-pool append overhead is quadratic at worst:
`k * (initialPoolLength + k)`. -/
theorem replayPoolCopyWork_le (pool : SPool) (steps : List SStep) :
    replayPoolCopyWork pool steps ≤
      steps.length * (pool.length + steps.length) := by
  induction steps generalizing pool with
  | nil => simp [replayPoolCopyWork]
  | cons s ss ih =>
      simp only [replayPoolCopyWork, List.length_cons]
      have hrec := ih (pool ++ [sentryOf pool s])
      simp only [List.length_append, List.length_cons, List.length_nil] at hrec
      nlinarith

/-! ## Sparse rule and solution input sizes -/

/-- Sparse row/reference cells presented to one rule check. Pool lookup traversal
is reported separately by `poolCopyCells`; this measure records the sparse data
reached by those lookups. -/
def reasonInputCells (pool : SPool) : SReason → Nat
  | .asm => 0
  | .lin comb =>
      (comb.map fun p => 1 + (spoolRow pool p.2).form.length).sum
  | .rnd comb =>
      (comb.map fun p => 1 + (spoolRow pool p.2).form.length).sum
  | .uns i1 l1 i2 l2 =>
      4 + (spoolRow pool i1).form.length + (spoolRow pool l1).form.length +
        (spoolRow pool i2).form.length + (spoolRow pool l2).form.length
  | .sol => 0

/-- Sparse input cells exposed to all derivation-rule checks in a full validation
pass. -/
def replayRuleInputCells (pool : SPool) : List SStep → Nat
  | [] => 0
  | s :: ss =>
      1 + s.stated.form.length + reasonInputCells pool s.reason +
        replayRuleInputCells (pool ++ [sentryOf pool s]) ss

/-- Number of `{ sol }` derivations, each of which may scan the complete `SOL`
section. -/
def solReasonCount : List SStep → Nat
  | [] => 0
  | s :: ss =>
      (match s.reason with | .sol => 1 | _ => 0) + solReasonCount ss

/-- Sparse constraint terms inspected when checking one solution valuation. -/
def constraintTermCells (v : Vipr) : Nat :=
  ((conSLes v).map fun c => 1 + c.form.length).sum

/-- Conservative source-level input-cell budget for one named solution.

Every valuation lookup may scan the sparse solution vector. The factor
`solution.length + 1` therefore accounts for the integer-variable, constraint,
and objective accesses made while checking that solution. -/
def oneSolutionInputCells (v : Vipr) (s : NamedSolution) : Nat :=
  (1 + v.intVars.length + constraintTermCells v + (objectiveForm v).length) *
    (s.2.length + 1)

/-- Input-cell budget for solution checking.

Two complete scans cover feasibility plus the objective witness in `solSectionB`;
each `{ sol }` derivation may perform one additional scan. This is conservative
for infeasibility results and for range results where short-circuiting succeeds
early. -/
def solutionInputCells (v : Vipr) : Nat :=
  (2 + solReasonCount (viprSteps v)) *
    ((v.sols.toList.map fun s => oneSolutionInputCells v s).sum)

/-! ## Full-checker budget -/

/-- A vector cost avoids pretending that one rule check, one list-cell copy, and
one arbitrary-precision arithmetic operation have the same machine cost. -/
structure CheckerWork where
  ruleChecks : Nat
  replaySteps : Nat
  poolCopyCells : Nat
  assumptionCells : Nat
  ruleInputCells : Nat
  solutionInputCells : Nat
deriving Repr, DecidableEq

/-- Conservative replay/control-flow budget for `checkViprResult`.

Validation builds the running pool once; the final-result check may replay it
once more.  The budget therefore charges two copies of the pool and assumption
construction work, even when short-circuiting avoids the second pass. -/
def checkerWorkUpper (v : Vipr) : CheckerWork :=
  let pool := sinitPool (conSLes v)
  let steps := viprSteps v
  { ruleChecks := steps.length
    replaySteps := steps.length
    poolCopyCells := 2 * replayPoolCopyWork pool steps
    assumptionCells := 2 * replayAssumptionWork pool steps
    ruleInputCells := replayRuleInputCells pool steps
    solutionInputCells := solutionInputCells v }

def CheckerWork.total (w : CheckerWork) : Nat :=
  w.ruleChecks + w.replaySteps + w.poolCopyCells + w.assumptionCells +
    w.ruleInputCells + w.solutionInputCells

/-- Pair the existing checker result with its verified structural budget.  The
checker itself is unchanged. -/
def checkViprResultProfiled (v : Vipr) : Bool × CheckerWork :=
  (checkViprResult v, checkerWorkUpper v)

theorem checkViprResultProfiled_value (v : Vipr) :
    (checkViprResultProfiled v).1 = checkViprResult v := rfl

theorem checkerWorkUpper_ruleChecks (v : Vipr) :
    (checkerWorkUpper v).ruleChecks = (viprSteps v).length := rfl

theorem checkerWorkUpper_replaySteps (v : Vipr) :
    (checkerWorkUpper v).replaySteps = (viprSteps v).length := rfl

theorem checkerWorkUpper_poolCopyCells_le (v : Vipr) :
    (checkerWorkUpper v).poolCopyCells ≤
      2 * (viprSteps v).length *
        ((conSLes v).length + (viprSteps v).length) := by
  have h := replayPoolCopyWork_le
    (sinitPool (conSLes v)) (viprSteps v)
  change 2 * replayPoolCopyWork (sinitPool (conSLes v)) (viprSteps v) ≤ _
  simpa only [sinitPool, List.length_map, Nat.mul_assoc] using
    Nat.mul_le_mul_left 2 h

theorem checkerWorkUpper_assumptionCells_le (v : Vipr) :
    (checkerWorkUpper v).assumptionCells ≤
      2 * (viprSteps v).length *
        (viprSteps v).length := by
  have h := certificate_replayAssumptionWork_le v
  change 2 * replayAssumptionWork (sinitPool (conSLes v)) (viprSteps v) ≤ _
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 h

/-- Main structural complexity theorem for the current list implementation.

Under the vector model, there are at most `k` rule checks and `k` final-replay
steps. Pool-list copying and finite-set assumption storage are both quadratic. -/
theorem checkViprResult_structural_cost (v : Vipr) :
    (checkerWorkUpper v).total ≤
      replayRuleInputCells (sinitPool (conSLes v)) (viprSteps v) +
      solutionInputCells v +
      2 * (viprSteps v).length +
      2 * (viprSteps v).length *
        ((conSLes v).length + (viprSteps v).length) +
      2 * (viprSteps v).length *
        (viprSteps v).length := by
  have hp := checkerWorkUpper_poolCopyCells_le v
  have ha := checkerWorkUpper_assumptionCells_le v
  simp only [checkerWorkUpper] at hp ha
  simp only [CheckerWork.total, checkerWorkUpper]
  nlinarith

end ViprCheck.Cert.ViprComplexity
