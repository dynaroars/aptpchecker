# Worked example (motivating example for the paper)

A complete, step-by-step trace of checking one APTP proof, using the toy network
`sample.onnx` (serialized exactly as [`sample.net`](sample.net)) and the proof
[`sample.aptp`](sample.aptp). Everything here is *exact*; decimals like `0.2` are
shown for readability but the checker uses the exact binary32 value
`0x3E4CCCCD = 13421773/67108864`. Written in full detail; trim for the paper.

> Numbers below (interval bounds, the affine reduction) were computed and
> cross-checked; the exact `ℚ` network outputs are validated bit-for-bit against
> an independent `fractions.Fraction` forward pass (see the pipeline test).

---

## 1. The network `𝒩`

A 2-input, 2-output ReLU MLP: `Linear₂ₓ₂ → ReLU → Linear₂ₓ₂ → ReLU → Linear₂ₓ₂`.

```
L0 (Linear):  W0 = [ -0.5  0.2 ]   b0 = [ -0.5 ]
                   [  0.3  0.2 ]        [  0.3 ]
ReLU  → hidden neurons N₁, N₂           (layer-1, global ids 1,2)
L2 (Linear):  W2 = [ -0.9  0.6 ]   b2 = [  0.2 ]
                   [  0.6  0.9 ]        [ -0.1 ]
ReLU  → hidden neurons N₃, N₄           (layer-2, global ids 3,4)
L4 (Linear):  W4 = [ -0.1  0.2 ]   b4 = [ -0.4 ]
                   [ -0.3  0.5 ]        [ -0.5 ]
```

Global neuron numbering (matching `ProofChecker.var_mapping`): the first ReLU
layer supplies `N₁,N₂`, the second `N₃,N₄` — 1-based, layer-major. The Lean
checker reconstructs exactly this from `sample.net`
(`reluWidths = #[2,2]`, `numNeurons = 4`).

Let `x = (x₀,x₁)` be the input, `p⁽¹⁾ = W0·x + b0` the layer-1 pre-activations,
`h⁽¹⁾ = ReLU(p⁽¹⁾)`, `p⁽²⁾ = W2·h⁽¹⁾ + b2`, `h⁽²⁾ = ReLU(p⁽²⁾)`, and
`y = W4·h⁽²⁾ + b4` the output. So `N₁,N₂` are the signs of `p⁽¹⁾`, and `N₃,N₄`
the signs of `p⁽²⁾`.

## 2. The query

From `sample.aptp`:

- **Input box** `ℬ`: `x₀ ∈ [-2, 2]`, `x₁ ∈ [-1, 1]`.
- **Property**: `(assert (<= Y_0 Y_1))` is the *negated* goal; the checker proves
  its negation everywhere, i.e. the objective row `c = (1, -1)`, `rhs = 0`, and
  the goal is
  ```
  ∀ x ∈ ℬ.   c · y  >  rhs      i.e.   y₀ − y₁ > 0   (Y₀ > Y₁).
  ```

The Lean parser yields exactly `numInputs=2, numOutputs=2, neurons=[1,2,3,4],
box=[[-2,2],[-1,1]], objectives=[(c=[1,-1], rhs=0)]`.

## 3. Neuron stability (exact interval bounds)

Propagating the box through `L0` with the interval rule
`lo = W⁺·lo_in + W⁻·hi_in + b`, `hi = W⁺·hi_in + W⁻·lo_in + b`:

| neuron | pre-activation range | status |
|---|---|---|
| `N₁` (`p⁽¹⁾₀`) | `[-1.7, 0.7]`   | unstable |
| `N₂` (`p⁽¹⁾₁`) | `[-0.5, 1.1]`   | unstable |

Then `h⁽¹⁾ ∈ [0,0.7]×[0,1.1]`, and through `L2`:

| neuron | pre-activation range | status |
|---|---|---|
| `N₃` (`p⁽²⁾₀`) | `[-0.43, 0.86]` | unstable |
| `N₄` (`p⁽²⁾₁`) | `[-0.1, 1.31]`  | unstable |

**All four neurons are unstable.** (These loose interval bounds are what the
encoding uses for the big-M constants; a tighter, still-sound bound only helps.)

## 4. The proof tree (4 leaves)

`sample.aptp` asserts the DNF (one `(and …)` per leaf); the Lean parser returns
`leaves = [[-4], [-2,4], [2,1,4], [2,-1,4]]`, i.e. over signs of `N₁,N₂,N₄`:

| leaf | literals | meaning |
|---|---|---|
| `L₁` | `¬N₄`              | `N₄` inactive |
| `L₂` | `¬N₂ ∧ N₄`         | `N₂` inactive, `N₄` active |
| `L₃` | `N₂ ∧ N₁ ∧ N₄`     | all three active |
| `L₄` | `N₂ ∧ ¬N₁ ∧ N₄`    | `N₂,N₄` active, `N₁` inactive |

**Note: the proof branches only on `N₁,N₂,N₄`; it never branches on `N₃`.** So
`N₃` remains an *unstable binary* neuron inside every leaf's MILP — which is why
each leaf is a genuine MILP, not an LP. (The earlier belief that `N₃` was
"stabilized" is incorrect: its interval range `[-0.43,0.86]` straddles 0.)

## 5. Coverage (Lemma: leaves tile the box)

Coverage requires: every `x ∈ ℬ` lies in some leaf's region. Since at any `x`
each neuron's pre-activation is either `≥ 0` or `< 0`, the sign vector
`(N₁,N₂,N₄) ∈ {0,1}³` is *some* Boolean assignment; we only need the DNF to be a
tautology over that cube (`N₃` is irrelevant — both its signs stay inside each
region):

```
¬N₄ ∨ (¬N₂∧N₄) ∨ (N₂∧N₁∧N₄) ∨ (N₂∧¬N₁∧N₄)
```

Case split: if `N₄=0`, `L₁` fires. If `N₄=1`: if `N₂=0`, `L₂`; if `N₂=1`, then
`N₁=1 ⇒ L₃`, `N₁=0 ⇒ L₄`. All 2³ assignments covered ⇒ tautology.

The checker decides this exactly as the reference does, but the *clean* way:
negate every literal and test the CNF `⋀_leaf ⋁ ¬ℓ` for UNSAT (equivalently prove
the tautology). This is a **sound over-approximation** of "covers all *reachable*
patterns" — sufficient for soundness, and it is the checker's coverage obligation.

## 6. Per-leaf refutation (the certificate step)

For each leaf we must show `∀ x ∈ ℬ ∩ R(leaf). y₀ − y₁ > 0`, i.e. the system
```
   x ∈ ℬ                                  (box)
   affine layer equalities                (v = W u + b)
   big-M ReLU for each unstable neuron     (with a binary a ∈ {0,1})
   the leaf's sign fixings                 (e.g. p⁽²⁾₁ < 0 for ¬N₄)
   c · y ≤ 0                               (negated property)
```
is **infeasible**. Because `N₃` (and, in a partial leaf, other unbranched
neurons) keep their binaries, this is a MILP; exact SCIP produces a VIPR
certificate (a tree of `lin`/`rnd`/`uns` steps) that the Lean checker replays in
`ℚ`. The base case each `lin` step reduces to is Farkas:
`y ≥ 0 ∧ yᵀA = 0 ∧ yᵀb < 0 ⇒ infeasible` (already proved:
`AptpCheck.Cert.farkas_infeasible`).

### 6a. A fully affine sub-case (to see a certificate concretely)

Fix a *complete* pattern, say all-active `N₁,N₂,N₃,N₄ ≥ 0`. Then every ReLU is
the identity, `𝒩` is affine, and
```
   y₀ − y₁ = 0.2·h⁽²⁾₀ − 0.3·h⁽²⁾₁ + 0.1            (from L4, since c=(1,-1))
           = 0.2·p⁽²⁾₀ − 0.3·p⁽²⁾₁ + 0.1            (all-active ⇒ h⁽²⁾=p⁽²⁾)
```
substituting `p⁽²⁾ = W2·h⁽¹⁾+b2` and `h⁽¹⁾ = p⁽¹⁾ = W0·x+b0` gives `y₀−y₁` as an
explicit affine function `α·x₀ + β·x₁ + γ`. On this region the refutation of
`y₀−y₁ ≤ 0` is a single Farkas `lin` step: a nonnegative combination of the box
bounds and the sign constraints whose result is `0 ≤ −ε` for some `ε > 0`. This
is the LP-only / complete-pattern mode — the easiest milestone target.

For the *actual* partial leaves (`L₁…L₄`), the unbranched `N₃` binary makes the
step a small branch-and-cut proof (`uns` over `p⁽²⁾₀ ≥ 0 ∨ p⁽²⁾₀ < 0`), still
fully checked in `ℚ`.

## 7. Verdict

```
CERTIFIED  ⟺  coverage holds  (§5)   ∧   every leaf refuted  (§6).
```
By composition (Theorem `certified_sound`): for all `x ∈ ℬ`, pick the covering
leaf; its refutation gives `y₀ − y₁ > 0`. Hence `Y₀ > Y₁` on the whole box. ∎

Spot check (exact `ℚ` eval, `y₀−y₁`): at the tightest corner `x=(2,1)`,
`y ≈ (-0.308, -0.313)`, so `y₀−y₁ ≈ +0.005 > 0` — the property is true and tight,
which is why a proof (rather than sampling) is needed.

---

## What is implemented vs. pending (maps to DESIGN.md roadmap)

- **Done & validated**: §1–§2 parsing (`Ast/Net`, `Ast/Aptp`), §1 exact eval
  (`Model/Network`, `Numeric/Float`), and the Farkas base case (`Cert/LinComb`).
- **Pending**: §3 encoding + encoding-soundness (`Model/Encoding`), §5 coverage
  checker (`Coverage/Tautology`), §6 VIPR replay (`Cert/Vipr` with `lin/rnd/uns`),
  and the composed `certified_sound` (`Pipeline/*`). The concrete VIPR file for
  each leaf comes from an exact-SCIP run (external, untrusted).
