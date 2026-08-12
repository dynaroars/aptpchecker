import Mathlib

/-!
# Feed-forward networks over `ℚ`

An executable, exact denotational semantics for the feed-forward fragment the
checker supports: dense affine (`Linear`), `ReLU`, and `Flatten`. Vectors are
`Array ℚ`; all arithmetic is exact.
-/

namespace AptpCheck.Model

/-- A dense affine layer: `y = W x + b`, with `W` row-major of length `outDim*inDim`. -/
structure Linear where
  outDim : Nat
  inDim : Nat
  W : Array ℚ
  b : Array ℚ
  deriving Repr, Inhabited

inductive Layer where
  | linear (l : Linear)
  | relu
  | flatten
  deriving Repr, Inhabited

structure Network where
  inDim : Nat
  layers : Array Layer
  deriving Repr, Inhabited

/-- `y_i = b_i + Σ_j W[i,j] · x_j`. -/
def Linear.apply (l : Linear) (x : Array ℚ) : Array ℚ :=
  (Array.range l.outDim).map (fun i =>
    (Array.range l.inDim).foldl (fun acc j => acc + l.W[i * l.inDim + j]! * x[j]!) (l.b[i]!))

def applyLayer : Layer → Array ℚ → Array ℚ
  | .linear l, x => l.apply x
  | .relu,     x => x.map (fun v => max v 0)
  | .flatten,  x => x

/-- Exact forward evaluation. -/
def Network.eval (net : Network) (x : Array ℚ) : Array ℚ :=
  net.layers.foldl (fun v ly => applyLayer ly v) x

/-- Number of hidden `ReLU` neurons, in the global layer-major order used to name
`N_k` (1-based) in APTP proofs. Each `ReLU` layer contributes `width` neurons,
where `width` is the output dimension of the preceding `Linear`. -/
def Network.reluWidths (net : Network) : Array Nat := Id.run do
  let mut widths : Array Nat := #[]
  let mut cur : Nat := net.inDim
  for ly in net.layers do
    match ly with
    | .linear l => cur := l.outDim
    | .relu     => widths := widths.push cur
    | .flatten  => pure ()
  return widths

def Network.numNeurons (net : Network) : Nat := net.reluWidths.foldl (· + ·) 0

end AptpCheck.Model
