import ViprCheck.Cert.ViprResultSound

/-!
# Termination of VIPR checking

Lean accepts the VIPR checker only because all of its recursive definitions are
total.  In particular, `sfreplay` and `resultDerivationB` recurse structurally on
the finite list of `DER` records.

This module records a more explicit, paper-facing termination argument:

* replay appends exactly one pool entry per derivation record;
* a fuel-bounded derivation checker agrees with `resultDerivationB` when supplied
  with exactly the number of derivation records; and
* parsing and checking any finite input text produces either a parser error or a
  Boolean result.

The fuel theorem bounds recursive derivation steps, not execution time.  A
single step can still contain arbitrarily many terms and arbitrarily large exact
rationals.
-/

namespace ViprCheck.Cert.ViprTermination

open ViprCheck.Ast ViprCheck.Pipeline
open ViprCheck.Cert
open ViprCheck.Cert.ViprResult

/-- Replay appends exactly one pool entry for every derivation record. -/
theorem sfreplay_length (pool : SPool) (steps : List SStep) :
    (sfreplay pool steps).length = pool.length + steps.length := by
  induction steps generalizing pool with
  | nil => simp [sfreplay]
  | cons s ss ih =>
      simp only [sfreplay]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- A fuel-bounded presentation of derivation checking.

`none` means that the supplied fuel was exhausted before all derivation records
were checked. -/
def resultDerivationFuel (v : Vipr) (pool : SPool) : Nat → List SStep → Option Bool
  | _, [] => some true
  | 0, _ :: _ => none
  | fuel + 1, s :: ss =>
      if resultStepB v pool s then
        resultDerivationFuel v (pool ++ [sentryOf pool s]) fuel ss
      else
        some false

/-- Exactly one unit of fuel per derivation record is sufficient, and the
fuel-bounded evaluator returns the same result as the actual checker. -/
theorem resultDerivationFuel_complete (v : Vipr) (pool : SPool) (steps : List SStep) :
    resultDerivationFuel v pool steps.length steps =
      some (resultDerivationB v pool steps) := by
  induction steps generalizing pool with
  | nil => simp [resultDerivationFuel, resultDerivationB]
  | cons s ss ih =>
      simp only [List.length_cons, resultDerivationFuel, resultDerivationB]
      by_cases h : resultStepB v pool s
      · simp [h, ih]
      · simp [h]

/-- On a parsed certificate, replay starts with one pool entry per `CON` row and
adds exactly one entry per `DER` record. -/
theorem certificate_replay_length (v : Vipr) :
    (sfreplay (sinitPool (conSLes v)) (viprSteps v)).length =
      (conSLes v).length + v.ders.size := by
  rw [sfreplay_length]
  simp [sinitPool, viprSteps]

/-- Logical termination of the full result checker on every finite parsed VIPR
certificate.  Lean's total-function discipline supplies the computational
termination argument; this theorem exposes its observable Boolean outcome. -/
theorem checkViprResult_terminates (v : Vipr) :
    checkViprResult v = true ∨ checkViprResult v = false := by
  cases checkViprResult v <;> simp

/-- Parse and check a concrete VIPR input using only total functions. -/
def parseAndCheckVipr (content : String) : Except String Bool := do
  let v ← parseVipr content
  return checkViprResult v

/-- Every finite VIPR input text produces either a parser error or a Boolean
checker result. -/
theorem parseAndCheckVipr_terminates (content : String) :
    (∃ msg, parseAndCheckVipr content = .error msg) ∨
      (∃ accepted, parseAndCheckVipr content = .ok accepted) := by
  cases h : parseAndCheckVipr content with
  | error msg => exact Or.inl ⟨msg, rfl⟩
  | ok accepted => exact Or.inr ⟨accepted, rfl⟩

end ViprCheck.Cert.ViprTermination
