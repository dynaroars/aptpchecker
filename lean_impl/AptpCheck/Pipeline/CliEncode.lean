import AptpCheck.Model.NetworkMLP
import AptpCheck.Model.EncodeFold
import AptpCheck.Pipeline.Affine

/-!
# Executable *verified* encoder for the CLI

`encodeVerified` builds each leaf's MILP from the **dimension-indexed** encoder
`MLP.encRows`/`MLP.objRow` — the very rows the soundness theorems
(`encoding_overapprox_mlp`, `certified_sound_mlp`) are proved about — rather than the
separate hand-optimized `Model.encode`. Since `encRows` is executable, the CLI can emit
exactly these rows, so there is no "executable-vs-model" gap in the encoding step: the
rows the solver sees are the rows the proof is about.

`MLP.binIds` lists the ReLU-indicator variable ids (only these are integer in the MILP).
-/

namespace AptpCheck.Model

open AptpCheck.Cert

/-- Build a leaf's MILP from the verified leaf-aware encoder `encFold`: box rows ++
`encFold`, the objective row, and the (unstable-neuron) binary ids. `none` if the
network is not an MLP. -/
def encodeVerified (net : Network) (box : Array (ℚ × ℚ)) (leaf : List Int)
    (c : Array ℚ) (rhs : ℚ) : Option (List Le × Le × List Nat) :=
  match toMLP net with
  | none => none
  | some ⟨_outD, mlp⟩ =>
      let lo : Fin net.inDim → ℚ := fun i => (box.getD i.val (0, 0)).1
      let hi : Fin net.inDim → ℚ := fun i => (box.getD i.val (0, 0)).2
      let cc := fun k => c.getD k.val 0
      some (Pipeline.boxRows lo hi ++ mlp.encFold 0 lo hi leaf 0, mlp.objRow 0 cc rhs,
            mlp.encFoldBinIds 0 lo hi leaf 0)

end AptpCheck.Model
