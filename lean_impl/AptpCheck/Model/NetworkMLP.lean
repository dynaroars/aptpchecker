import Mathlib
import AptpCheck.Model.Network
import AptpCheck.Model.EncodingSound

/-!
# Bridging the executable `Network` and the proof-side `MLP`

`Model/Network` gives the *executable* feed-forward semantics over `Array ℚ`
(`Linear`, `ReLU`, `Flatten`, `Network.eval`).  `Model/EncodingSound` proves the
per-leaf refutation theorems (`certified_sound_mlp`, `certified_sound_mlp_satLeaf`)
for the dimension-indexed proof type `MLP`.

This module connects them:

* `toMLP : Network → Option (Σ outD, MLP net.inDim outD)` parses an executable network
  into the `Linear, (ReLU, Linear)*` normal form (`Flatten` is elided as the identity),
  returning `none` on any other shape or dimension mismatch.

* `toMLP_eval` proves that when the conversion succeeds, the executable evaluation and the
  proof-side `MLP.eval` agree entrywise (on the `Fin`-view of the input array).

* `certified_sound_network` / `certified_sound_network_satLeaf` compose the eval agreement
  with `certified_sound_mlp{,_satLeaf}` so that the proven per-leaf refutation applies to
  the *parsed, runnable* `Network`.
-/

namespace AptpCheck.Model

open AptpCheck.Cert AptpCheck.Pipeline AptpCheck.Coverage

/-! ## Stripping `Flatten` (the identity layer) -/

/-- `true` for `Flatten` layers only. -/
def isFlatten : Layer → Bool
  | .flatten => true
  | _ => false

/-- Drop every `Flatten` layer.  Since `applyLayer .flatten` is the identity, this leaves
`Network.eval` unchanged (see `foldl_stripFlatten`). -/
def stripFlatten (layers : List Layer) : List Layer :=
  layers.filter (fun ly => !isFlatten ly)

/-- The `Fin`-indexed weight matrix read out of a `Linear` layer, using the *same* total
`getD` indexing as `Linear.apply`. -/
def linW (l : Linear) (d : ℕ) : Fin l.outDim → Fin d → ℚ :=
  fun i j => l.W.getD (i.val * l.inDim + j.val) 0

/-- The `Fin`-indexed bias read out of a `Linear` layer. -/
def linB (l : Linear) : Fin l.outDim → ℚ :=
  fun i => l.b.getD i.val 0

/-! ## The conversion -/

/-- Convert a `Flatten`-free layer list, with current dimension `d`, into an `MLP`.

The list must be `Linear, (ReLU, Linear)*` ending in `Linear`, with each `Linear`'s input
dimension equal to the current dimension.  Returns `none` on any other shape or dimension
mismatch. -/
def toMLPCore : (d : ℕ) → List Layer → Option (Σ outD : ℕ, MLP d outD)
  | d, [Layer.linear l] =>
      if l.inDim = d then
        some ⟨l.outDim, MLP.last (linW l d) (linB l)⟩
      else none
  | d, Layer.linear l :: Layer.relu :: rest =>
      if l.inDim = d then
        (toMLPCore l.outDim rest).map
          (fun r => ⟨r.1, MLP.cons (linW l d) (linB l) r.2⟩)
      else none
  | _, _ => none

/-- Convert an executable `Network` into the proof-side `MLP` normal form. -/
def toMLP (net : Network) : Option (Σ outD : ℕ, MLP net.inDim outD) :=
  toMLPCore net.inDim (stripFlatten net.layers.toList)

/-- Architecture (layer widths) of an `MLP`: `[inD, hid₁, …, outD]`.  Only used to inspect
the converted shape. -/
def MLP.arch : {inD outD : ℕ} → MLP inD outD → List ℕ
  | inD, outD, .last _ _ => [inD, outD]
  | inD, _, .cons _ _ rest => inD :: rest.arch

/-! ## Array/Finset bridging helpers -/

/-- `a[i]!` is the total `getD` used everywhere in `Linear.apply` (the `ℚ` default is `0`). -/
private lemma getBang0 (a : Array ℚ) (i : ℕ) : a[i]! = a.getD i 0 := rfl

/-- Extract the `k`-th entry of a mapped `Array.range`. -/
private lemma getD_map_range (m : ℕ) (g : ℕ → ℚ) (k : Fin m) :
    ((Array.range m).map g).getD k.val 0 = g k.val := by
  have hk : k.val < ((Array.range m).map g).size := by
    simp only [Array.size_map, Array.size_range]; exact k.isLt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some,
    Array.getElem_map, Array.getElem_range]

/-- A `foldl` over `List.range n` with an additive step equals the initial value plus the
`Fin`-indexed sum. -/
private lemma foldl_listrange_add (n : ℕ) (g : ℕ → ℚ) (init : ℚ) :
    (List.range n).foldl (fun acc j => acc + g j) init = init + ∑ j : Fin n, g j.val := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil]
      ring

/-! ## Per-layer evaluation agreement -/

/-- The size of a `Linear` layer's output. -/
lemma linApply_size (l : Linear) (v : Array ℚ) : (l.apply v).size = l.outDim := by
  rw [Linear.apply, Array.size_map, Array.size_range]

/-- The `k`-th output of `Linear.apply` in `preAct` sum form (still over `v`'s `getD`). -/
lemma linApply_getD (l : Linear) (v : Array ℚ) (k : Fin l.outDim) :
    (l.apply v).getD k.val 0
      = l.b.getD k.val 0
        + ∑ j : Fin l.inDim, l.W.getD (k.val * l.inDim + j.val) 0 * v.getD j.val 0 := by
  have h1 : (l.apply v).getD k.val 0
      = (Array.range l.inDim).foldl
          (fun acc j => acc + l.W[k.val * l.inDim + j]! * v[j]!) (l.b[k.val]!) := by
    rw [Linear.apply]; exact getD_map_range l.outDim _ k
  rw [h1, getBang0 l.b k.val, ← Array.foldl_toList, Array.toList_range,
    show (fun (acc : ℚ) (j : ℕ) => acc + l.W[k.val * l.inDim + j]! * v[j]!)
        = (fun (acc : ℚ) (j : ℕ) => acc + l.W.getD (k.val * l.inDim + j) 0 * v.getD j 0) from by
      funext acc j; rw [getBang0, getBang0],
    foldl_listrange_add]

/-- **Per-layer agreement (`Linear`).**  On the `Fin`-view `vf` of the input array `v`, the
executable `Linear.apply` output matches the proof-side `preAct` of the read-out weights. -/
lemma linear_agree (l : Linear) (d : ℕ) (hl : l.inDim = d) (v : Array ℚ) (vf : Fin d → ℚ)
    (hv : ∀ j : Fin d, v.getD j.val 0 = vf j) (k : Fin l.outDim) :
    (l.apply v).getD k.val 0 = preAct (linW l d) (linB l) vf k := by
  subst hl
  rw [linApply_getD]
  simp only [preAct, linW, linB]
  rw [add_comm (l.b.getD k.val 0)]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [hv j])

/-- Extract the `k`-th entry of a `ReLU`-mapped array (in range). -/
private lemma relu_getD (w : Array ℚ) (k : ℕ) (hk : k < w.size) :
    (w.map (fun t => max t 0)).getD k 0 = max (w.getD k 0) 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hk]

/-- **Per-layer agreement (`Linear` then `ReLU`).**  The executable `ReLU ∘ Linear` output
matches the proof-side `postAct`. -/
lemma linear_relu_agree (l : Linear) (d : ℕ) (hl : l.inDim = d) (v : Array ℚ) (vf : Fin d → ℚ)
    (hv : ∀ j : Fin d, v.getD j.val 0 = vf j) (k : Fin l.outDim) :
    (applyLayer Layer.relu (l.apply v)).getD k.val 0 = postAct (linW l d) (linB l) vf k := by
  show ((l.apply v).map (fun t => max t 0)).getD k.val 0 = postAct (linW l d) (linB l) vf k
  rw [relu_getD _ _ (by rw [linApply_size]; exact k.isLt), postAct,
    linear_agree l d hl v vf hv]

/-! ## `Flatten` is the identity -/

/-- Dropping `Flatten` layers leaves the fold (hence `Network.eval`) unchanged. -/
lemma foldl_stripFlatten (layers : List Layer) (v : Array ℚ) :
    (stripFlatten layers).foldl (fun w ly => applyLayer ly w) v
      = layers.foldl (fun w ly => applyLayer ly w) v := by
  induction layers generalizing v with
  | nil => rfl
  | cons ly rest ih =>
      cases ly with
      | linear l =>
          have hs : stripFlatten (Layer.linear l :: rest)
              = Layer.linear l :: stripFlatten rest := by simp [stripFlatten, isFlatten]
          rw [hs, List.foldl_cons, List.foldl_cons, ih]
      | relu =>
          have hs : stripFlatten (Layer.relu :: rest)
              = Layer.relu :: stripFlatten rest := by simp [stripFlatten, isFlatten]
          rw [hs, List.foldl_cons, List.foldl_cons, ih]
      | flatten =>
          have hs : stripFlatten (Layer.flatten :: rest) = stripFlatten rest := by
            simp [stripFlatten, isFlatten]
          rw [hs, List.foldl_cons, ih]
          rfl

/-! ## Full evaluation agreement -/

/-- **Core eval agreement.**  When `toMLPCore d layers` succeeds, folding the executable
layers over an array `v` whose `getD`-view is `vf` agrees entrywise with `MLP.eval`. -/
theorem toMLPCore_eval : ∀ (d : ℕ) (layers : List Layer)
    (r : Σ outD : ℕ, MLP d outD), toMLPCore d layers = some r →
    ∀ (v : Array ℚ) (vf : Fin d → ℚ), (∀ j : Fin d, v.getD j.val 0 = vf j) →
    ∀ i : Fin r.1,
      (layers.foldl (fun w ly => applyLayer ly w) v).getD i.val 0 = r.2.eval vf i := by
  intro d layers
  induction d, layers using toMLPCore.induct with
  | case1 l =>
      intro r hr v vf hv i
      simp only [toMLPCore, if_true] at hr
      obtain rfl := Option.some.inj hr
      simp only [List.foldl_cons, List.foldl_nil, applyLayer, MLP.eval]
      exact linear_agree l l.inDim rfl v vf hv i
  | case2 d l hne =>
      intro r hr v vf hv i
      simp only [toMLPCore] at hr
      rw [if_neg hne] at hr
      exact absurd hr (by simp)
  | case3 l rest ih =>
      intro r hr v vf hv i
      simp only [toMLPCore, if_true] at hr
      cases hc : toMLPCore l.outDim rest with
      | none => rw [hc] at hr; simp at hr
      | some r' =>
          rw [hc] at hr
          simp only [Option.map_some] at hr
          obtain rfl := Option.some.inj hr
          simp only [List.foldl_cons, MLP.eval]
          exact ih r' hc (applyLayer Layer.relu (l.apply v))
            (postAct (linW l l.inDim) (linB l) vf)
            (fun k => linear_relu_agree l l.inDim rfl v vf hv k) i
  | case4 d l rest hne =>
      intro r hr v vf hv i
      simp only [toMLPCore] at hr
      rw [if_neg hne] at hr
      exact absurd hr (by simp)
  | case5 t d hn1 hn2 =>
      intro r hr v vf hv i
      exfalso
      rcases t with _ | ⟨ly1, _ | ⟨ly2, rest⟩⟩
      · exact absurd hr (by simp [toMLPCore])
      · cases ly1 with
        | linear l => exact hn1 l rfl
        | relu => exact absurd hr (by simp [toMLPCore])
        | flatten => exact absurd hr (by simp [toMLPCore])
      · cases ly1 with
        | linear l =>
            cases ly2 with
            | relu => exact hn2 l rest rfl
            | linear l2 => exact absurd hr (by simp [toMLPCore])
            | flatten => exact absurd hr (by simp [toMLPCore])
        | relu => exact absurd hr (by simp [toMLPCore])
        | flatten => exact absurd hr (by simp [toMLPCore])

/-- **Top-level eval agreement.**  When `toMLP net = some ⟨outD, mlp⟩`, the executable
`Network.eval` agrees entrywise with `mlp.eval` on the `getD`-view of the input array. -/
theorem toMLP_eval (net : Network) (r : Σ outD : ℕ, MLP net.inDim outD)
    (h : toMLP net = some r) (x : Array ℚ) (i : Fin r.1) :
    (Network.eval net x).getD i.val 0 = r.2.eval (fun j => x.getD j.val 0) i := by
  rw [Network.eval, ← Array.foldl_toList, ← foldl_stripFlatten]
  exact toMLPCore_eval net.inDim (stripFlatten net.layers.toList) r h
    x (fun j => x.getD j.val 0) (fun _ => rfl) i

/-! ## Bridged soundness: the proven refutation applies to the parsed `Network` -/

/-- **Per-leaf refutation for a parsed `Network`.**  If `net` converts to the MLP `r.2`,
`x` (as its `Fin`-view) lies in the box `[lo,hi]`, the leaf `L` is consistent with the
network's real signs, and a Farkas certificate refutes the emitted rows together with the
negated objective, then the objective strictly exceeds `rhs` on the *executable*
`Network.eval` output. -/
theorem certified_sound_network (net : Network) (r : Σ outD : ℕ, MLP net.inDim outD)
    (hconv : toMLP net = some r)
    (cc : Fin r.1 → ℚ) (rhs : ℚ) (lo hi : Fin net.inDim → ℚ) (L : List Int) (x : Array ℚ)
    (hx : ∀ j, lo j ≤ x.getD j.val 0 ∧ x.getD j.val 0 ≤ hi j)
    (hcon : r.2.consistent 0 (fun j => x.getD j.val 0) L)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (r.2.objRow 0 cc rhs :: (boxRows lo hi ++ r.2.encRows 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel :
      (comb.map (fun p => p.1 * p.2.form.eval (r.2.trace (fun j => x.getD j.val 0)))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * (Network.eval net x).getD k.val 0 := by
  have hmlp := certified_sound_mlp r.2 cc rhs lo hi L (fun j => x.getD j.val 0)
    hx hcon comb hsub hnn hcancel hneg
  rw [show (∑ k, cc k * (Network.eval net x).getD k.val 0)
        = ∑ k, cc k * r.2.eval (fun j => x.getD j.val 0) k from
      Finset.sum_congr rfl (fun k _ => by rw [toMLP_eval net r hconv x k])]
  exact hmlp

/-- **Per-leaf refutation for a parsed `Network`, `satLeaf` form.**  As
`certified_sound_network`, but the leaf-consistency hypothesis is phrased through the
coverage `satLeaf` interface (`σ` is the true sign vector, and `L` is satisfied by `σ`). -/
theorem certified_sound_network_satLeaf (net : Network) (r : Σ outD : ℕ, MLP net.inDim outD)
    (hconv : toMLP net = some r)
    (cc : Fin r.1 → ℚ) (rhs : ℚ) (lo hi : Fin net.inDim → ℚ) (L : List Int) (σ : Nat → Bool)
    (x : Array ℚ)
    (hx : ∀ j, lo j ≤ x.getD j.val 0 ∧ x.getD j.val 0 ≤ hi j)
    (hmatch : r.2.signMatch 0 (fun j => x.getD j.val 0) σ) (hsat : satLeaf L σ = true)
    (comb : List (ℚ × Le))
    (hsub : ∀ p ∈ comb,
      p.2 ∈ (r.2.objRow 0 cc rhs :: (boxRows lo hi ++ r.2.encRows 0 lo hi L 0)))
    (hnn : ∀ p ∈ comb, 0 ≤ p.1)
    (hcancel :
      (comb.map (fun p => p.1 * p.2.form.eval (r.2.trace (fun j => x.getD j.val 0)))).sum = 0)
    (hneg : (comb.map (fun p => p.1 * p.2.rhs)).sum < 0) :
    rhs < ∑ k, cc k * (Network.eval net x).getD k.val 0 := by
  have hmlp := certified_sound_mlp_satLeaf r.2 cc rhs lo hi L σ (fun j => x.getD j.val 0)
    hx hmatch hsat comb hsub hnn hcancel hneg
  rw [show (∑ k, cc k * (Network.eval net x).getD k.val 0)
        = ∑ k, cc k * r.2.eval (fun j => x.getD j.val 0) k from
      Finset.sum_congr rfl (fun k _ => by rw [toMLP_eval net r hconv x k])]
  exact hmlp

end AptpCheck.Model
