import AptpCheck.Model.NetworkMLP
import AptpCheck.Model.EncodeFold

/-!
# Per-leaf soundness for the leaf-aware encoder, transported to the parsed `Network`

These mirror `certified_sound_network`/`_satLeaf` (which were stated over the uniform
`encRows`) but over the leaf-aware `encFold`. With these in place, the whole soundness
chain runs on the encoder the tool actually uses, and the uniform `encRows` can be
retired.
-/

namespace AptpCheck.Model

open AptpCheck.Cert AptpCheck.Pipeline AptpCheck.Coverage

/-- Per-leaf refutation for the leaf-aware encoder, `satLeaf` form (plugs into
`Pipeline.certified_sound_abstract`). -/
theorem certified_sound_mlp_fold_satLeaf {inD outD : ℕ} (net : MLP inD outD)
    (cc : Fin outD → ℚ) (rhs : ℚ) (lo hi : Fin inD → ℚ) (L : List Int) (σ : Nat → Bool)
    (x : Fin inD → ℚ) (hx : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hmatch : net.signMatch 0 x σ) (hsat : satLeaf L σ = true)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (net.objRow 0 cc rhs :: (boxRows lo hi ++ net.encFold 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel : (comb.map (fun p => p.1 * p.2.form.eval (net.trace x))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * net.eval x k :=
  certified_sound_mlp_fold net cc rhs lo hi L x hx
    (net.consistent_of_signMatch 0 x σ L hmatch hsat) comb hsub hnn hcancel hneg

/-- Per-leaf refutation for a parsed `Network` via the leaf-aware encoder. -/
theorem certified_sound_network_fold (net : Network) (r : Σ outD : ℕ, MLP net.inDim outD)
    (hconv : toMLP net = some r)
    (cc : Fin r.1 → ℚ) (rhs : ℚ) (lo hi : Fin net.inDim → ℚ) (L : List Int) (x : Array ℚ)
    (hx : ∀ j, lo j ≤ x.getD j.val 0 ∧ x.getD j.val 0 ≤ hi j)
    (hcon : r.2.consistent 0 (fun j => x.getD j.val 0) L)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (r.2.objRow 0 cc rhs :: (boxRows lo hi ++ r.2.encFold 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel :
      (comb.map (fun p => p.1 * p.2.form.eval (r.2.trace (fun j => x.getD j.val 0)))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * (Network.eval net x).getD k.val 0 := by
  have hmlp := certified_sound_mlp_fold r.2 cc rhs lo hi L (fun j => x.getD j.val 0)
    hx hcon comb hsub hnn hcancel hneg
  rw [show (∑ k, cc k * (Network.eval net x).getD k.val 0)
        = ∑ k, cc k * r.2.eval (fun j => x.getD j.val 0) k from
      Finset.sum_congr rfl (fun k _ => by rw [toMLP_eval net r hconv x k])]
  exact hmlp

/-- Per-leaf refutation for a parsed `Network`, `satLeaf` form. -/
theorem certified_sound_network_fold_satLeaf (net : Network) (r : Σ outD : ℕ, MLP net.inDim outD)
    (hconv : toMLP net = some r)
    (cc : Fin r.1 → ℚ) (rhs : ℚ) (lo hi : Fin net.inDim → ℚ) (L : List Int) (σ : Nat → Bool)
    (x : Array ℚ)
    (hx : ∀ j, lo j ≤ x.getD j.val 0 ∧ x.getD j.val 0 ≤ hi j)
    (hmatch : r.2.signMatch 0 (fun j => x.getD j.val 0) σ) (hsat : satLeaf L σ = true)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (r.2.objRow 0 cc rhs :: (boxRows lo hi ++ r.2.encFold 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel :
      (comb.map (fun p => p.1 * p.2.form.eval (r.2.trace (fun j => x.getD j.val 0)))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * (Network.eval net x).getD k.val 0 :=
  certified_sound_network_fold net r hconv cc rhs lo hi L x hx
    (r.2.consistent_of_signMatch 0 (fun j => x.getD j.val 0) σ L hmatch hsat)
    comb hsub hnn hcancel hneg

end AptpCheck.Model
