import AptpCheck.Coverage.Tautology

/-!
# Top-level composition

The end-to-end soundness theorem `certified_sound` factors into **coverage** (the
leaves tile the input space) and **per-leaf refutation** (each leaf's region has no
counterexample). This module proves that composition against the real
`coverage_sound`, abstracting the two pieces still under construction:

* `sig x` — the true ReLU sign vector at input `x` (to be produced by the network
  trace in `Model/Encoding`'s assembly);
* `refute` — per-leaf refutation (to be discharged by the encoding over-approximation
  plus the VIPR certificate replay in `Cert/Vipr`).

Instantiating `sig` and `refute` with those (forthcoming) proofs yields the concrete
`certified_sound` of Fig. 2 in the paper with no further logical glue.
-/

namespace AptpCheck.Pipeline

open AptpCheck.Coverage

/-- **End-to-end composition (soundness skeleton).** If the coverage check passes and
every leaf's region is free of counterexamples, then the property holds on the whole
domain. This is the proof of the paper's top-level theorem, modulo the two interfaces
`sig` and `refute`. -/
theorem certified_sound_abstract
    {Input : Type*}
    (leaves : List Leaf) (mem prop : Input → Prop) (sig : Input → Nat → Bool)
    (hcover : checkCoverage leaves = true)
    (refute : ∀ leaf ∈ leaves, ∀ x, mem x → satLeaf leaf (sig x) = true → prop x)
    {x : Input} (hx : mem x) : prop x := by
  obtain ⟨leaf, hlmem, hsat⟩ := coverage_sound leaves hcover (sig x)
  exact refute leaf hlmem x hx hsat

end AptpCheck.Pipeline
