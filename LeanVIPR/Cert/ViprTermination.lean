import LeanVIPR.Cert.ViprCheckerSound

/-!
# Termination of VIPR checking

The production checker recurses structurally over the finite list of `DER`
records. This module exposes the corresponding replay-size and fuel results.
The fuel counts derivation records, not arithmetic or finite-set operations.
-/

namespace LeanVIPR.Cert.ViprTermination

open LeanVIPR.Ast LeanVIPR.Pipeline
open LeanVIPR.Cert.ViprChecker

/-- Every successful replay appends exactly one array entry per derivation record. -/
theorem replaySteps_size (v : Vipr) :
    ∀ (pool : CheckerPool) (steps : List SStep) (final : CheckerPool),
      replaySteps? v pool steps = some final →
      final.size = pool.size + steps.length := by
  intro pool steps
  induction steps generalizing pool with
  | nil =>
      intro final h
      simp only [replaySteps?] at h
      cases h
      simp
  | cons s ss ih =>
      intro final h
      simp only [replaySteps?] at h
      by_cases hs : stepValidB v pool s = true
      · simp only [hs, if_true] at h
        have hsize := ih (pool.push (entryOf pool s)) final h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize
      · simp [hs] at h

/-- Fuel-bounded presentation of the production replay. The outer option reports
fuel exhaustion; the inner option is the checker's accept/reject replay result. -/
def replayFuel (v : Vipr) (pool : CheckerPool) : Nat → List SStep → Option (Option CheckerPool)
  | _, [] => some (some pool)
  | 0, _ :: _ => none
  | fuel + 1, s :: ss =>
      if stepValidB v pool s then
        replayFuel v (pool.push (entryOf pool s)) fuel ss
      else
        some none

/-- One fuel unit per derivation record is sufficient and agrees with the actual
array-backed replay. -/
theorem replayFuel_complete (v : Vipr) (pool : CheckerPool) (steps : List SStep) :
    replayFuel v pool steps.length steps = some (replaySteps? v pool steps) := by
  induction steps generalizing pool with
  | nil => simp [replayFuel, replaySteps?]
  | cons s ss ih =>
      simp only [List.length_cons, replayFuel, replaySteps?]
      by_cases hs : stepValidB v pool s = true
      · simp [hs, ih]
      · simp [hs]

/-- Logical termination of the production checker on every finite parsed certificate. -/
theorem checkVipr_terminates (v : Vipr) :
    checkVipr v = true ∨ checkVipr v = false := by
  cases checkVipr v <;> simp

/-- Parse and check a concrete VIPR input using only total functions. -/
def parseAndCheckVipr (content : String) : Except String Bool := do
  let v ← parseVipr content
  return checkVipr v

/-- Every finite VIPR input text produces either a parser error or a Boolean result. -/
theorem parseAndCheckVipr_terminates (content : String) :
    (∃ msg, parseAndCheckVipr content = .error msg) ∨
      (∃ accepted, parseAndCheckVipr content = .ok accepted) := by
  cases h : parseAndCheckVipr content with
  | error msg => exact Or.inl ⟨msg, rfl⟩
  | ok accepted => exact Or.inr ⟨accepted, rfl⟩

end LeanVIPR.Cert.ViprTermination
