import Mathlib

/-!
# Coverage: the proof-tree leaves tile the activation cube

Each leaf is a partial ReLU activation pattern (signed neuron ids). Coverage is
the obligation that every input's sign vector satisfies some leaf — i.e. the DNF
`⋁_leaf ⋀ literals` is a tautology over the Boolean cube of the mentioned neurons.
We decide it by enumerating that cube and prove the decision sound: it implies
coverage for *every* assignment `σ : ℕ → Bool`. This is the propositional
"visits all nodes" obligation (Lemma `coverage_sound`).
-/

namespace AptpCheck.Coverage

/-- A leaf: signed neuron ids (`+k` active, `−k` inactive). -/
abbrev Leaf := List Int

/-- Does the assignment `σ` (neuron id ↦ active?) satisfy every literal of `leaf`? -/
def satLeaf (leaf : Leaf) (σ : Nat → Bool) : Bool :=
  leaf.all (fun ℓ => if 0 < ℓ then σ ℓ.natAbs else !(σ ℓ.natAbs))

/-- Is `σ` covered by some leaf? -/
def covered (leaves : List Leaf) (σ : Nat → Bool) : Bool :=
  leaves.any (fun leaf => satLeaf leaf σ)

/-- All total assignments obtained by fixing the neurons in the list (others `false`). -/
def assignmentsOn : List Nat → List (Nat → Bool)
  | [] => [fun _ => false]
  | k :: ks =>
      (assignmentsOn ks).flatMap (fun σ => [Function.update σ k false, Function.update σ k true])

/-- The distinct neurons mentioned by the leaves. -/
def mentioned (leaves : List Leaf) : List Nat :=
  (leaves.flatMap (fun leaf => leaf.map Int.natAbs)).dedup

/-- The coverage check: every assignment over the mentioned neurons is covered. -/
def checkCoverage (leaves : List Leaf) : Bool :=
  (assignmentsOn (mentioned leaves)).all (fun σ => covered leaves σ)

/-- Enumeration completeness: for any `σ`, some enumerated assignment agrees with it
on the fixed (nodup) neuron list. -/
theorem assignmentsOn_complete :
    ∀ (ns : List Nat), ns.Nodup → ∀ (σ : Nat → Bool),
      ∃ σ' ∈ assignmentsOn ns, ∀ k ∈ ns, σ' k = σ k := by
  intro ns
  induction ns with
  | nil => intro _ σ; exact ⟨fun _ => false, by simp [assignmentsOn], by simp⟩
  | cons k ks ih =>
      intro hnd σ
      have hcons := List.nodup_cons.mp hnd
      obtain ⟨τ, hτmem, hτag⟩ := ih hcons.2 σ
      refine ⟨Function.update τ k (σ k), ?_, ?_⟩
      · simp only [assignmentsOn, List.mem_flatMap]
        exact ⟨τ, hτmem, by cases hσk : σ k <;> simp [hσk]⟩
      · intro j hj
        rcases List.mem_cons.mp hj with hjk | hjks
        · subst hjk; simp
        · have hjne : j ≠ k := fun h => hcons.1 (h ▸ hjks)
          rw [Function.update_of_ne hjne]; exact hτag j hjks

/-- If two assignments agree on every neuron a leaf mentions, they agree on `satLeaf`. -/
theorem satLeaf_congr {leaf : Leaf} {σ σ' : Nat → Bool}
    (hag : ∀ ℓ ∈ leaf, σ' ℓ.natAbs = σ ℓ.natAbs)
    (h : satLeaf leaf σ' = true) : satLeaf leaf σ = true := by
  simp only [satLeaf, List.all_eq_true] at h ⊢
  intro ℓ hℓ
  have := h ℓ hℓ
  rwa [hag ℓ hℓ] at this

/-- **Coverage soundness.** If the check passes, then *every* assignment
`σ : ℕ → Bool` (in particular the true sign vector of any input) satisfies some
leaf. -/
theorem coverage_sound (leaves : List Leaf) (h : checkCoverage leaves = true)
    (σ : Nat → Bool) : ∃ leaf ∈ leaves, satLeaf leaf σ = true := by
  obtain ⟨σ', hσ'mem, hσ'ag⟩ :=
    assignmentsOn_complete (mentioned leaves) (List.nodup_dedup _) σ
  simp only [checkCoverage, List.all_eq_true] at h
  have hcov : covered leaves σ' = true := h σ' hσ'mem
  simp only [covered, List.any_eq_true] at hcov
  obtain ⟨leaf, hleafmem, hsat'⟩ := hcov
  refine ⟨leaf, hleafmem, ?_⟩
  refine satLeaf_congr (fun ℓ hℓ => ?_) hsat'
  apply hσ'ag
  simp only [mentioned, List.mem_dedup, List.mem_flatMap]
  exact ⟨leaf, hleafmem, List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩⟩

end AptpCheck.Coverage
