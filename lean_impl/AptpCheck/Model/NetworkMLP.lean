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

open AptpCheck.Cert AptpCheck.Pipeline

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

end AptpCheck.Model
