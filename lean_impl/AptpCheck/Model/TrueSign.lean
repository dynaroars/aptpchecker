import AptpCheck.Model.EncodingSound

/-!
# The network's global true-sign vector and its `signMatch`

`Pipeline.certified_sound_abstract` needs a `sig : Input → Nat → Bool` that assigns a
Boolean sign to every neuron of every input. This module defines that vector for a general
`MLP` — `MLP.trueSign` — as the true ReLU sign of each neuron's pre-activation, laid out
over the whole (1-based, `gid0`-offset) global neuron numbering. It then proves
`MLP.signMatch_trueSign`: this vector *is* the network's neuron-sign vector at `x`
(`signMatch`), which is exactly the hypothesis `MLP.consistent_of_signMatch` consumes.

A small congruence lemma `MLP.signMatch_congr` (signMatch inspects `σ` only at ids
`> gid0`) bridges the recursive step, where the layer-local `trueSign` and the sub-network's
own `trueSign` agree on every id beyond the current layer window.

Everything is kernel-checked and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace AptpCheck.Model

/-- The network's true ReLU sign vector over ALL neurons (1-based global ids offset by
`gid0`): neuron id `nn` is active iff its pre-activation is `≥ 0`. Ids outside the current
layer's window `(gid0, gid0+hidD]` delegate to the sub-network. -/
def MLP.trueSign : {inD outD : ℕ} → MLP inD outD → (Fin inD → ℚ) → ℕ → (Nat → Bool)
  | _, _, .last _ _, _, _ => fun _ => false
  | inD, _, .cons (hidD := hidD) W b rest, xv, gid0 => fun nn =>
      if h : gid0 < nn ∧ nn ≤ gid0 + hidD then
        decide (0 ≤ preAct W b xv ⟨nn - gid0 - 1, by omega⟩)
      else rest.trueSign (postAct W b xv) (gid0 + hidD) nn

/-- Inside the layer window, `trueSign` at id `gid0+i+1` is exactly the sign of `preAct i`. -/
lemma MLP.trueSign_cons_mem {inD hidD outD : ℕ}
    (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ) (rest : MLP hidD outD)
    (xv : Fin inD → ℚ) (gid0 : ℕ) (i : Fin hidD) :
    (MLP.cons W b rest).trueSign xv gid0 (gid0 + i.val + 1)
      = decide (0 ≤ preAct W b xv i) := by
  have hcond : gid0 < gid0 + i.val + 1 ∧ gid0 + i.val + 1 ≤ gid0 + hidD :=
    ⟨by omega, by omega⟩
  have hidx : gid0 + i.val + 1 - gid0 - 1 = i.val := by omega
  simp only [MLP.trueSign, dif_pos hcond, hidx, Fin.eta]

/-- Beyond the layer window, `trueSign (cons …)` delegates to the sub-network's own
`trueSign`. -/
lemma MLP.trueSign_cons_gt {inD hidD outD : ℕ}
    (W : Fin hidD → Fin inD → ℚ) (b : Fin hidD → ℚ) (rest : MLP hidD outD)
    (xv : Fin inD → ℚ) (gid0 nn : ℕ) (h : gid0 + hidD < nn) :
    (MLP.cons W b rest).trueSign xv gid0 nn
      = rest.trueSign (postAct W b xv) (gid0 + hidD) nn := by
  have hcond : ¬ (gid0 < nn ∧ nn ≤ gid0 + hidD) := by omega
  simp only [MLP.trueSign, dif_neg hcond]

/-- `signMatch` only inspects `σ` at ids `> gid0`, so it transports along any two sign
vectors that agree above `gid0`. -/
lemma MLP.signMatch_congr {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (gid0 : ℕ) (xv : Fin inD → ℚ) (σ σ' : Nat → Bool),
      (∀ nn, gid0 < nn → σ nn = σ' nn) →
      net.signMatch gid0 xv σ → net.signMatch gid0 xv σ' := by
  induction net with
  | last W b => intro gid0 xv σ σ' _ _; simp only [MLP.signMatch]
  | @cons inD hidD outD W b rest ih =>
      intro gid0 xv σ σ' hcong hmatch
      simp only [MLP.signMatch] at hmatch ⊢
      refine ⟨fun i => ?_, ?_⟩
      · rw [← hcong (gid0 + i.val + 1) (by omega)]; exact hmatch.1 i
      · exact ih (gid0 + hidD) (postAct W b xv) σ σ'
          (fun nn hnn => hcong nn (by omega)) hmatch.2

/-- **The true-sign vector satisfies `signMatch`.** For every input `xv` and offset `gid0`,
`MLP.trueSign xv gid0` is the network's genuine neuron-sign vector. -/
lemma MLP.signMatch_trueSign {inD outD : ℕ} (net : MLP inD outD) :
    ∀ (xv : Fin inD → ℚ) (gid0 : ℕ), net.signMatch gid0 xv (net.trueSign xv gid0) := by
  induction net with
  | last W b => intro xv gid0; simp only [MLP.signMatch]
  | @cons inD hidD outD W b rest ih =>
      intro xv gid0
      simp only [MLP.signMatch]
      refine ⟨fun i => ?_, ?_⟩
      · exact MLP.trueSign_cons_mem W b rest xv gid0 i
      · -- bridge the sub-network's own `trueSign` to the layer-local one via congruence
        refine MLP.signMatch_congr rest (gid0 + hidD) (postAct W b xv)
          (rest.trueSign (postAct W b xv) (gid0 + hidD))
          ((MLP.cons W b rest).trueSign xv gid0) ?_ (ih (postAct W b xv) (gid0 + hidD))
        intro nn hnn
        exact (MLP.trueSign_cons_gt W b rest xv gid0 nn hnn).symm

end AptpCheck.Model
