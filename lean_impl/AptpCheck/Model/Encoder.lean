import AptpCheck.Model.Network
import AptpCheck.Model.Encoding

/-!
# The MILP encoder (executable)

Turns `network + input box + leaf` into the list of `Le` rows (and the objective row)
that a VIPR certificate refutes. Variables are numbered as signals are created:
inputs first, then each layer's outputs; unstable ReLU neurons also get a post var and
a binary. This is the *executable* side of item 1; its soundness proof
(`encoding_overapprox`, that the real trace satisfies every emitted row) is developed
separately using `boxRows_sat`, `reluRows_sat`, and the affine equalities.
-/

namespace AptpCheck.Model

open AptpCheck.Cert

/-- Negate every coefficient of a linear form. -/
def LinForm.neg (f : LinForm) : LinForm := f.map (fun t => ⟨t.idx, -t.coeff⟩)

/-- Encoder state carried across layers. -/
structure Enc where
  next : Nat            -- next free variable id
  ids : Array Nat       -- variable ids of the current signal vector
  lo : Array ℚ          -- current exact lower bounds
  hi : Array ℚ          -- current exact upper bounds
  neuron : Nat          -- global ReLU-neuron counter (0-based, layer-major)
  rows : Array Le
  deriving Inhabited

/-- Allocate input variables `0..n-1` and emit the box rows. -/
def initEnc (box : Array (ℚ × ℚ)) : Enc :=
  let n := box.size
  { next := n
    ids := Array.range n
    lo := box.map (·.1)
    hi := box.map (·.2)
    neuron := 0
    rows := (Array.range n).foldl (fun rs j =>
              (rs.push ⟨[⟨j, 1⟩], (box[j]!).2⟩).push ⟨[⟨j, -1⟩], -(box[j]!).1⟩) #[] }

/-- Encode a `Linear` layer: fresh output vars, an equality row per output, and exact
interval bounds `W⁺·lo + W⁻·hi + b .. W⁺·hi + W⁻·lo + b`. -/
def encLinear (e : Enc) (l : Linear) : Enc := Id.run do
  let base := e.next
  let mut rows := e.rows
  let mut nids : Array Nat := #[]
  let mut nlo : Array ℚ := #[]
  let mut nhi : Array ℚ := #[]
  for i in [0:l.outDim] do
    let vid := base + i
    nids := nids.push vid
    -- equality  vid = Σ_j W[i,j]·x_j + b_i   as   (vid − Σ W x) {≤,≥} b_i
    let mut form : LinForm := [⟨vid, 1⟩]
    for j in [0:l.inDim] do
      form := ⟨e.ids[j]!, -(l.W[i * l.inDim + j]!)⟩ :: form
    let bi := l.b[i]!
    rows := (rows.push ⟨form, bi⟩).push ⟨LinForm.neg form, -bi⟩
    -- interval bounds
    let mut lo := bi
    let mut hi := bi
    for j in [0:l.inDim] do
      let w := l.W[i * l.inDim + j]!
      if 0 ≤ w then
        lo := lo + w * e.lo[j]!
        hi := hi + w * e.hi[j]!
      else
        lo := lo + w * e.hi[j]!
        hi := hi + w * e.lo[j]!
    nlo := nlo.push lo
    nhi := nhi.push hi
  return { e with next := base + l.outDim, ids := nids, lo := nlo, hi := nhi, rows := rows }

/-- Encode a `ReLU` layer. A neuron stable-active (or fixed active by the leaf) becomes
`post = pre`; stable-inactive (or fixed inactive) becomes `post = 0`; otherwise the four
big-M rows plus a binary. Fixed neurons also emit their sign constraint. -/
def encRelu (e : Enc) (leaf : List Int) : Enc := Id.run do
  let mut rows := e.rows
  let mut nids : Array Nat := #[]
  let mut nlo : Array ℚ := #[]
  let mut nhi : Array ℚ := #[]
  let mut next := e.next
  let mut ncount := e.neuron
  for k in [0:e.ids.size] do
    let preId := e.ids[k]!
    let lo := e.lo[k]!
    let hi := e.hi[k]!
    let gid := ncount + 1                              -- 1-based global neuron id
    ncount := ncount + 1
    let fixedActive := leaf.contains (Int.ofNat gid)
    let fixedInactive := leaf.contains (-(Int.ofNat gid))
    if decide (0 ≤ lo) || fixedActive then             -- active: post = pre
      nids := nids.push preId
      nlo := nlo.push (max lo 0); nhi := nhi.push hi
      if fixedActive then rows := rows.push ⟨[⟨preId, -1⟩], 0⟩      -- pre ≥ 0
    else if decide (hi ≤ 0) || fixedInactive then      -- inactive: post = 0
      let vid := next; next := next + 1
      nids := nids.push vid
      rows := (rows.push ⟨[⟨vid, 1⟩], 0⟩).push ⟨[⟨vid, -1⟩], 0⟩     -- post = 0
      nlo := nlo.push 0; nhi := nhi.push 0
      if fixedInactive then rows := rows.push ⟨[⟨preId, 1⟩], 0⟩     -- pre ≤ 0
    else                                               -- unstable, unbranched: big-M
      let vid := next
      let bid := next + 1
      next := next + 2
      nids := nids.push vid
      for r in reluRows lo hi preId vid bid do rows := rows.push r
      nlo := nlo.push 0; nhi := nhi.push hi
  return { e with next := next, ids := nids, lo := nlo, hi := nhi, neuron := ncount, rows := rows }

/-- Full encoding: the constraint rows and the objective row `Σ_k c_k · out_k ≤ rhs`
(its negation is what the certificate refutes). -/
def encode (net : Network) (box : Array (ℚ × ℚ)) (leaf : List Int)
    (c : Array ℚ) (rhs : ℚ) : List Le × Le :=
  let e := net.layers.foldl (fun e ly =>
      match ly with
      | .linear l => encLinear e l
      | .relu => encRelu e leaf
      | .flatten => e) (initEnc box)
  let objForm : LinForm := (List.range e.ids.size).map (fun k => ⟨e.ids.getD k 0, c.getD k 0⟩)
  (e.rows.toList, ⟨objForm, rhs⟩)

end AptpCheck.Model
