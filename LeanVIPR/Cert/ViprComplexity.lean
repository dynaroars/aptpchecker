import LeanVIPR.Cert.ViprTermination

/-!
# Structural complexity of the array-backed VIPR checker

This source-level cost model follows the production implementation. It counts
one rule check and one array write per derivation record, sparse referenced-row
input, finite-set assumption work, and solution-vector input. Array allocation,
arbitrary-precision bit complexity, and compiler/runtime constants are outside
the model.
-/

namespace LeanVIPR.Cert.ViprComplexity

open LeanVIPR.Ast LeanVIPR.Pipeline
open LeanVIPR.Cert LeanVIPR.Cert.ViprChecker LeanVIPR.Ast.Vipr

def reasonReferenceCount : SReason → Nat
  | .asm | .sol => 0
  | .lin comb | .rnd comb => comb.length
  | .uns _ _ _ _ => 4

def totalReferenceCount (steps : List SStep) : Nat :=
  (steps.map fun s => reasonReferenceCount s.reason).sum

/-- Sparse cells read by one rule check, resolving references in the parsed
certificate's global row numbering. -/
def reasonInputCells (v : Vipr) : SReason → Nat
  | .asm | .sol => 0
  | .lin comb | .rnd comb =>
      (comb.map fun p => 1 + (viprRow v p.2).form.length).sum
  | .uns i1 l1 i2 l2 =>
      4 + (viprRow v i1).form.length + (viprRow v l1).form.length +
        (viprRow v i2).form.length + (viprRow v l2).form.length

def replayRuleInputCells (v : Vipr) : Nat :=
  ((viprSteps v).map fun s =>
    1 + s.stated.form.length + reasonInputCells v s.reason).sum

def solReasonCount : List SStep → Nat
  | [] => 0
  | s :: ss =>
      (match s.reason with | .sol => 1 | _ => 0) + solReasonCount ss

def constraintTermCells (v : Vipr) : Nat :=
  ((conSLes v).map fun c => 1 + c.form.length).sum

def oneSolutionInputCells (v : Vipr) (s : NamedSolution) : Nat :=
  (1 + v.intVars.length + constraintTermCells v + (objectiveForm v).length) *
    (s.2.length + 1)

def solutionInputCells (v : Vipr) : Nat :=
  (2 + solReasonCount (viprSteps v)) *
    ((v.sols.toList.map fun s => oneSolutionInputCells v s).sum)

/-- Vector budget for the production checker. `assumptionCells` bounds resident
open assumptions by `k²`; `assumptionMergeCells` bounds referenced finite-set
inputs by `k` times the number of row references. -/
structure CheckerWork where
  ruleChecks : Nat
  arrayWrites : Nat
  ruleInputCells : Nat
  assumptionCells : Nat
  assumptionMergeCells : Nat
  solutionInputCells : Nat
deriving Repr, DecidableEq

def checkerWorkUpper (v : Vipr) : CheckerWork :=
  let steps := viprSteps v
  let k := steps.length
  { ruleChecks := k
    arrayWrites := k
    ruleInputCells := replayRuleInputCells v
    assumptionCells := k * k
    assumptionMergeCells := k * totalReferenceCount steps
    solutionInputCells := solutionInputCells v }

def CheckerWork.total (w : CheckerWork) : Nat :=
  w.ruleChecks + w.arrayWrites + w.ruleInputCells + w.assumptionCells +
    w.assumptionMergeCells + w.solutionInputCells

def checkViprProfiled (v : Vipr) : Bool × CheckerWork :=
  (checkVipr v, checkerWorkUpper v)

theorem checkViprProfiled_value (v : Vipr) :
    (checkViprProfiled v).1 = checkVipr v := rfl

theorem checkerWorkUpper_ruleChecks (v : Vipr) :
    (checkerWorkUpper v).ruleChecks = (viprSteps v).length := rfl

theorem checkerWorkUpper_arrayWrites (v : Vipr) :
    (checkerWorkUpper v).arrayWrites = (viprSteps v).length := rfl

/-- Exact expansion of the production checker's structural upper-bound model. -/
theorem checkVipr_structural_cost (v : Vipr) :
    (checkerWorkUpper v).total =
      2 * (viprSteps v).length +
      replayRuleInputCells v +
      (viprSteps v).length * (viprSteps v).length +
      (viprSteps v).length * totalReferenceCount (viprSteps v) +
      solutionInputCells v := by
  simp [CheckerWork.total, checkerWorkUpper]
  omega

end LeanVIPR.Cert.ViprComplexity
