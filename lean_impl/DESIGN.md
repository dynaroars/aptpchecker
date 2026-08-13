# AptpCheck — a formally-verified APTP proof checker in Lean 4

A from-scratch Lean 4 reimplementation of [`aptpchecker`](../README.md): a tool that
checks **Activation-Pattern-Tree Proofs (APTP)** produced by neural-network
verifiers (α,β-CROWN, GCP-CROWN, …). The original is Python + Gurobi and is
*trusted by inspection*. This reimplementation is **exact** (rational arithmetic),
uses **SCIP** as an *untrusted* oracle whose proof certificate is re-checked
inside Lean, and comes with a **machine-checked soundness theorem**.

> Status (builds against Mathlib). **Front-end complete & validated** against the
> reference Python: exact `float32/64 → ℚ` (`Numeric/Float`), the S-expression lexer
> (`Ast/Sexpr`), the `.net` parser (`Ast/Net`) + exact network eval (`Model/Network`)
> — matched bit-for-bit vs. an independent `Fraction` forward pass — and the `.aptp`
> parser (`Ast/Aptp`) — leaves/box/objective match `read_aptp.py` on both sample
> forms. The Farkas base case (`Cert/LinComb`, `farkas_infeasible`) and the **coverage
> check** (`Coverage/Tautology`, `coverage_sound` — the "leaves tile the box"
> obligation) are proved and axiom-clean (no `sorry`, no `native_decide`); coverage
> is validated on the sample leaves. A full worked example is in the paper
> (`paper/main.tex §"A worked example"`) and `examples/WORKED-EXAMPLE.md`.
> The two **encoding-soundness cornerstones** are proved and axiom-clean in
> `Model/Encoding`: `reluBigM_sound` (exact ReLU ⟹ the four big-M constraints) and
> `affine_interval_sound` (exact interval bounds are valid), plus `stable_active`/
> `stable_inactive`. The **top-level composition skeleton** is proved and axiom-clean
> (`Pipeline/Compose.certified_sound_abstract`: coverage ⊕ per-leaf refutation ⟹ the
> property, against the real `coverage_sound`), abstracting the two remaining
> interfaces. The **certificate→refutation glue** is proved and axiom-clean in `Cert/LinCon`:
> sparse linear constraints (`Le` over a `ℕ→ℚ` valuation), `farkas_le`
> (nonneg combination cancelling to a negative constant ⟹ infeasible — the VIPR
> `lin`-to-absurdity step), and `refute_of_cert` (encoding rows satisfied by the
> trace + a Farkas combination over `rows + {objVar ≤ rhs}` ⟹ `objVar > rhs`, i.e.
> per-leaf refutation once `objVar = c·net(x)`). The objective row uses `Model/Encoding.fuse_linear`
> (proved: `c·(Wx+b) = (Σ_i c_i W_{i·})·x + Σ_i c_i b_i` — the `W_last ← c·W_last`
> fusion), and `Cert/LinCon.refute_of_cert` now takes an arbitrary objective *row*.
> The **affine / complete-pattern case is closed end-to-end and kernel-checked**
> (`Pipeline/Affine`): `boxRows`+`boxRows_sat`, `objForm`+`objForm_eval`,
> `affine_refuted`, and `certified_sound_singleLinear` (derives `c·net(x) > ρ` on the
> whole box from a Farkas certificate, composing `refute_of_cert` + `fuse_linear`).
> The **ReLU big-M rows** are also done: `Model/Encoding.reluRows` + `reluRows_sat`
> (real trace satisfies the four big-M constraints, from `reluBigM_sound`). So both
> per-layer building blocks (`boxRows_sat`, `reluRows_sat`) + the objective
> (`fuse_linear`) + the composition (`refute_of_cert`, `certified_sound_abstract`)
> are proved. **Encoder soundness (Problem 1) is proved for arbitrary-depth MLPs**
> (`Model/EncodingSound`: `encoding_overapprox_mlp`, `certified_sound_mlp`, and
> `certified_sound_mlp_satLeaf` — the last phrased through the coverage `satLeaf`
> interface so it composes with `Pipeline.certified_sound_abstract`; for
> `Lin→ReLU→…→Lin` with the full big-M encoding, by induction on depth; axiom-clean;
> one-hidden/affine cases retained). Stated on a dimension-indexed `MLP` normal form
> ending in a linear layer; Conv/CNN out of scope. **VIPR replay
> (Problem 2) is complete** — a full automatic proof-by-cases certificate checker
> (`Cert/Vipr`: `lin_sound`/`rnd_sound`/`uns_sound`; `RefTree` + `refTree_sound`; the
> runnable `Bool` `checkRefTree` + `checkRefTree_sound`, verified running on an
> integer-infeasible example; `Pipeline/ViprCheck.vipr_infeasible` composing it with
> the VIPR v1.0 parser `Ast/Vipr`, demonstrated end-to-end on a hand-written `.vipr`).
> The refutation tree is produced by an untrusted step and re-validated, so it stays
> out of the TCB. All axiom-clean. **The `.net` parser is FULLY verified**
> (`Ast/NetRoundtrip.parseNet_printNet : parseNet (printNet r) = .ok (rawToNet r)`,
> axiom-clean) — this required de-`partial`-izing the layer loop: `Ast/Net.parseLayers`
> is now total via `parseLayersFuel` (fuel `= toks.length+1`, behavior-preserving,
> regression-checked to give byte-identical exact outputs on the sample). **The `.aptp`
> parser is also FULLY verified** (`Ast/AptpRoundtrip.parseAptp_printAptp :
> parseAptp (printAptp raw) = .ok (decode raw)`, axiom-clean) — this required
> de-`partial`-izing the S-expression parser (`parseSexpFuel`/`parseListFuel`) and
> rewriting the two-pass `parseAptp` loops as total `List.foldl`s (behavior-preserving,
> regression-checked on both sample proofs). So **both parsers are out of the trusted
> base**. All modules are wired into the root and the full `lake build` passes (17139
> jobs). **Pending**: (a) bridge the dimension-indexed `MLP` soundness model to the
> executable `Array`-based `Model/Encoder`; (b) Conv/CNN encoding (future); (c) the
> executable CLI wiring (Problem 3), including the untrusted flat-VIPR→`RefTree`
> converter feeding `checkRefTree`.

---

## 1. What the checker guarantees

Inputs: a feed-forward network `net`, an input box `[lo, ub]`, and a linear output
property `(c, rhs)` (a row vector `c` over the outputs and a scalar `rhs`).

**Top-level soundness theorem** (the thing we machine-check):

```
theorem certified_sound :
    check net box aptp vipr = .certified →
    ∀ x, x ∈ box → c ⬝ net x > rhs
```

i.e. if the checker accepts, then for *every* input in the box the property holds.
This mirrors the original tool's contract: it minimizes `c · y − rhs` per leaf and
reports `CERTIFIED` iff every leaf's minimum is `> 0`.

### 1.1 Decomposition (this is the "sound + complete / visits all BaB nodes" goal)

An APTP proof is a set of **leaves**. Each leaf `L` is a partial ReLU activation
pattern: a finite set of literals `±k` meaning "neuron `k` is active (pre-activation
`≥ 0`)" or "inactive (`< 0`)". Soundness factors into two independent obligations:

1. **Per-leaf refutation.**  For each leaf `L`, the region
   `R(L) = { x ∈ box : the sign pattern of net's pre-activations at x is consistent with L }`
   contains no counterexample:  `∀ x ∈ R(L), c ⬝ net x > rhs`.
   This is discharged by an **exact-rational certificate** (§3): SCIP proves the
   MILP `(encoding of net) ∧ (x ∈ box) ∧ (splits of L) ∧ (c·y ≤ rhs)` infeasible,
   and we re-check its VIPR derivation in ℚ.

2. **Coverage.**  Every `x ∈ box` lies in some `R(L)`:
   `∀ x ∈ box, ∃ L ∈ leaves, x ∈ R(L)`.
   This is the propositional check at the end of `read_aptp.py`.

Given (1) and (2): take any `x ∈ box`; by (2) it lies in some `R(L)`; by (1) for
that `L`, `c ⬝ net x > rhs`. ∎  "Visiting all nodes of the BaB tree" is exactly
obligation (2) — the leaves *tile* the input space — combined with the fact that
every leaf carries a refutation certificate.

### 1.2 Termination / exhaustiveness of the driver

The reference driver keeps a queue of unsolved leaves; a solved leaf *subsumes* (via
`Node.__lt__`) and filters every leaf whose region is a subset of it, and the queue
strictly shrinks each round. `CERTIFIED` is returned only when the queue empties, so
every leaf is either directly certified or subsumed by a certified more-general leaf.
Subsumption is sound because refuting a larger region refutes its sub-regions
(monotonicity of "no counterexample" under region inclusion). In Lean we do not need
the queue at all for *soundness*: we simply require a certificate for every leaf and
the coverage proof. The queue is an *efficiency* device; we model it (and prove its
subsumption sound) only when we port the optimized driver.

---

## 2. Key findings that shape the design

These were established by reading the Python source + the certificate literature,
and independently re-verified.

- **The coverage check is a *sound over-approximation*.**  `read_aptp.py` builds
  `CNF(from_clauses=proof)` (each leaf's conjunction of literals fed in as a clause)
  and asserts it is UNSAT. This decides "the DNF `⋁_L ⋀ literals` is a tautology"
  — but only over **free independent booleans** `N_k`, and only correctly because
  flipping the polarity of *every* literal is a satisfiability-preserving bijection
  (so `UNSAT(⋀_L ⋁ ℓ)` = `UNSAT(⋀_L ⋁ ¬ℓ)` = "negation of the DNF is UNSAT" =
  "DNF is a tautology").  A tautology over the free boolean cube is **sufficient**
  (every real sign vector is *some* assignment, hence covered) but **not necessary**
  (it may reject a proof that only covers reachable patterns). We implement the
  clean, obviously-correct version: negate every literal, check the CNF is UNSAT
  (equivalently, prove the tautology directly). This is sound for coverage.

- **Unbranched neurons stay binary; folded-stable neurons must be re-verified.**
  In `sample.aptp` the proof branches only on `N_1,N_2,N_4`; `N_3` is *not* branched
  on. Its exact interval range on the box is `[-0.43, 0.86]` — i.e. **unstable** — so
  it remains a free binary neuron inside every leaf's MILP (a concrete reason each
  leaf is a MILP, not an LP; see the next bullet). Coverage only needs the branched
  neurons; an unbranched neuron is covered trivially since both its signs lie inside
  each region. Separately, *if* a producer folds a neuron it claims stable, the
  checker must re-verify that stability with **exact interval bounds** as part of
  encoding-soundness (§4). (An earlier note calling `N_3` "stabilized" was wrong —
  corrected here.)

- **Each APTP leaf is itself a small MILP, not an LP.**  Leaves are *partial*
  patterns; neurons not listed in a leaf keep their binary ReLU indicator. So a
  per-leaf certificate is a full VIPR derivation (`lin` + `rnd` + `uns`), not a
  single Farkas multiplier vector. (If we ever *required complete* patterns, each
  leaf's network would be affine and reduce to a single-`lin` Farkas check — a
  useful simplification for an early milestone, but not the default.)

- **The hard part is encoding-soundness, not the certificate check.**  Checking a
  Farkas/VIPR certificate over ℚ is elementary. Proving that the rational constraint
  system faithfully *over-approximates* `net` on the region (affine layers, big-M
  ReLU, spec fusion `W_last ← c·W_last`, exact interval bounds, stability) is the
  central theorem. Looseness is safe; the only way to be unsound is an encoding that
  is *too tight* (excludes a real point). See §4.

---

## 3. External-solver certificates (SCIP + VIPR)

We replace Gurobi with **exact SCIP** (SCIP-Ex / SoPlex), which emits a **VIPR**
certificate (*Verifying Integer Programming Results*, Cheung–Gleixner–Steffy).
SCIP is **never trusted**; only its VIPR output is, and only after we re-derive it in ℚ.

A `.vipr` file has sections `VER / VAR / INT / OBJ / CON / RTP / SOL / DER`. The heart
is the `DER` list of derived constraints, each with a *reason*:

- `lin` — a **nonnegative rational combination** of earlier constraints (LP dual /
  Farkas step). Sign-consistency ("suitable") makes it a genuine implication.
- `rnd` — `lin` followed by integer rounding (valid for integer variables): certifies
  Gomory/MIR cuts and integrality.
- `uns` — combines the two children of an integer split `x_i ≤ k ∨ x_i ≥ k+1`
  (exhaustive over ℤ), *discharging* that branch assumption.
- `asm` / `sol` — a branching hypothesis / a primal solution.

Acceptance: for `RTP infeas`, the final derived constraint is an **absurdity with
empty assumption set** (a global Farkas infeasibility certificate); for `RTP range`,
the final derived constraint has empty assumption set and dominates the claimed bound.

**The only mathematics the checker relies on** is the *easy* direction of Farkas:

```
y ≥ 0  ∧  yᵀA = 0  ∧  yᵀb < 0   →   { x | A x ≤ b } = ∅
```

Proof: if `x` were feasible, `0 = (yᵀA)x = yᵀ(Ax) ≤ yᵀb < 0`. One contradiction from
`Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left`. Mathlib's real Farkas' lemma
(`ProperCone.hyperplane_separation_point`, topological existence direction) is **not
needed** for soundness — only for *completeness* (a research side-quest, not our
milestone).

Prior art we follow: `viprchk`/`viprcomp` (the C++ VIPR checkers we re-implement and
verify), Coq `micromega`'s "untrusted oracle + reflective verified checker" model, and
Marabou's proof production (proof tree with Farkas leaves + ReLU split lemmas).

---

## 4. Encoding-soundness (the central theorem)

`Model/Encoding.lean` turns `net + box + leaf L` into a rational system `A x ≤ b`
plus an objective row, matching `milp_solver.py`:

- **Linear layer**: `v = W · prev + b`; interval bounds `lower = W⁺·lb + W⁻·ub + b`,
  `upper = W⁺·ub + W⁻·lb + b` — exact in ℚ.
- **ReLU**: stable-active → identity; stable-inactive → `0`; unstable → post-var with
  the four big-M constraints and a binary indicator. Stability is decided by the exact
  interval bounds (`lb ≥ 0`, `ub ≤ 0`, else unstable).
- **Spec fusion**: the last layer folds `c` in (`W_last ← c·W_last`, `b_last ← c·b_last`),
  so the single terminal variable equals `c · net(x)`.

The theorem to prove:

```
theorem encoding_overapprox (L : Leaf) (x : Fin nIn → ℚ) (hx : x ∈ box)
    (hL : consistentWith L x) :
    ∃ z, satisfies (encode net box L) z ∧ z.output = c ⬝ net x
```

i.e. every real `(x, internal activations)` consistent with `L` is a *feasible point*
of the encoded system with objective value `c · net x`. Combined with the
certificate's "no feasible point has objective `≤ rhs`", this yields per-leaf
refutation (§1.1.1). Note the direction: we need feasible-set ⊇ real behavior
(over-approximation); tighter-than-reality bounds would be unsound, looser ones are fine.

---

## 5. Data contract (on-disk formats)

Per verification task, files share a stem `<stem>`:

### 5a. `<stem>.net` — exact network (INPUT; generation is out of scope)

Per the decision to **not touch Python/ONNX**, the Lean tool reads only this exact,
lossless text format. (An ONNX→`.net` exporter, if ever written, lives entirely
outside this tool and its output is cross-checked, never trusted.)

```
NET v1
INPUT <d0> [<d1> ...]                 ; input shape excluding batch, e.g. "2" or "1 28 28"
LAYER Linear <out> <in>
  W <val>...  (out×in, row-major)
  B <val>...  (out)
LAYER ReLU
LAYER Flatten
LAYER Conv2d <oc> <ic> <kh> <kw> <sh> <sw> <ph> <pw>
  W <val>...  (oc×ic×kh×kw, row-major)
  B <val>...  (oc)
END
```

`<val>` is an exact literal — a rational `p/q` (recommended: `q` a power of two, so it
is exactly a float32/64 value) or a C99 hex-float (`0x1.abcp-3`). Decimal is accepted
only if it round-trips. **No decimal re-parsing of floats** — every weight is an exact
dyadic rational.

### 5b. `<stem>.aptp` — the proof tree (INPUT; grammar unchanged from the original)

SMT-LIB-flavored S-expressions. The Lean lexer reproduces `read_statements`
(strip `;` comments, join multi-line by paren balance, collapse whitespace, drop the
space after `(`/`)`). Grammar (both single- and multi-name declares are supported):

```
(declare-const X_0 X_1 Real)          ; inputs;  num_inputs = max index + 1
(declare-const Y_0 Y_1 Real)          ; outputs
(declare-pwl N_1 N_2 N_3 N_4 ReLU)    ; hidden ReLU neurons (case-insensitive)
(assert (>= X_0 -2.0)) (assert (<= X_0 2.0)) ...   ; input box (RHS must be numeric)
(assert (<= Y_0 Y_1))                 ; output property → one (c, rhs) row
(assert (or (and (< N_4 0))           ; hidden DNF = the proof tree
            (and (< N_2 0) (>= N_4 0))
            (and (>= N_2 0) (>= N_1 0) (>= N_4 0))
            (and (>= N_2 0) (< N_1 0) (>= N_4 0))))
```

Output-property encoding (normalized to `≤`): `Y_a ≤ Y_b` → row `+1@a, −1@b, rhs 0`;
`Y_a ≤ c` → `+1@a, rhs c`; `c ≤ Y_b` → `−1@b, rhs −c`. Each output assert is a separate
objective; the property holds iff **all** certify. Hidden literals: `(>= N_k 0)` → `+k`
(active), `(< N_k 0)` → `−k` (inactive); split point must be `0`.

Neuron global numbering `N_k` (must match the network): hidden ReLU neurons numbered
1-based, layer-major then neuron-index, exactly as `ProofChecker.var_mapping`.

### 5c. `<stem>.leaf<KEY>.vipr` — per-leaf certificate + `<stem>.manifest`

One VIPR file per leaf, keyed by the sorted signed-literal tuple of the leaf's `(and …)`
clause (= `Node.history`), e.g. leaf `(and (>= N_2 0)(< N_1 0)(>= N_4 0))` → literals
`[-1, 2, 4]` → key `-1_2_4`. A manifest maps leaf-key → cert path. `CERTIFIED` iff the
coverage check passes **and** every leaf key has a valid certificate proving
`min(c·y − rhs) > 0` (or infeasibility ⇒ vacuously discharged).

---

## 6. Trusted computing base (TCB)

Trusted (documented, to be minimized / hardened):
- The Lean kernel + `Rat` arithmetic (unavoidable; kernel-checked, **no `native_decide`**).
- The `.net` and `.aptp` parsers (differential-fuzz vs. the Python parser; a verified
  parser is future work).
- The `.net` file faithfully representing the intended network (generation out of scope).

**Not trusted** (fully re-checked in Lean): SCIP / SoPlex, the VIPR certificate, and
`viprcomp`/`viprttn` if used.

---

## 7. Module layout

```
AptpCheck/
  Numeric/Float.lean      float32/float64 bit-pattern → exact ℚ (dyadic)
  Ast/Sexpr.lean          S-expr lexer: read_statements normalization + tokenizer
  Ast/Aptp.lean           .aptp → Problem (box, objectives, leaves) + coverage input
  Ast/Net.lean            .net exact-network parser
  Ast/Vipr.lean           VIPR v1.0 parser (VAR/INT/OBJ/CON/RTP/SOL/DER)
  Model/Network.lean      MLP over ℚ (Linear/ReLU/Flatten[/Conv2d]); net(x) semantics
  Model/Encoding.lean     network+box+leaf → (A,b) system; exact intervals; ENCODING SOUNDNESS
  Cert/LinComb.lean       Farkas 'lin' check + soundness lemma  (smallest sound unit)
  Cert/Round.lean         'rnd' integer-rounding derivation
  Cert/Unsplit.lean       'uns' integer-split discharge + assumption-set tracking
  Cert/Vipr.lean          fold DER → MILP infeasibility / dual-bound soundness
  Coverage/Tautology.lean DNF coverage (negate-literals CNF UNSAT) + soundness
  Pipeline/Problem.lean   link .net + .aptp + .vipr; VIPR↔Lean (A,b,c) correspondence
  Pipeline/Verdict.lean   end-to-end verdict; CERTIFIED ↔ ∀x∈box, c·net x > rhs
  Pipeline/Soundness.lean top-level theorem composing Encoding ⊕ Vipr ⊕ Coverage
Main.lean                 CLI: aptpcheck --net … --aptp … [--vipr-dir …]
```

---

## 8. Roadmap (earliest sound checker first)

- **M0 — de-risk.**  Build Lean+Mathlib; confirm the `Finset.sum`/`Matrix.mulVec`
  lemmas exist; hand-build the `sample` leaf system in ℚ and kernel-check a trivial
  `checkLin`; run exact SCIP on `sample` and capture a real `.vipr`.
- **M1 — numeric + parsers.**  `Numeric/Float`, `Ast/Sexpr`, `Ast/Aptp`, `Ast/Net`.
  Differential-test parsers vs. `read_aptp.py` on both sample files.
- **M2 — network + encoding (MLP only).**  `Model/Network`, `Model/Encoding`; prove
  encoding-soundness for the affine-per-leaf case first.
- **M3 — Farkas leaf checker.**  `Cert/LinComb` + its one soundness lemma.
- **M4 — first end-to-end SOUND result on `sample`** (LP-only / complete-pattern
  simplification): `aptpcheck` returns `certified` with a kernel-checked
  `∀ x ∈ box, Y_0 > Y_1`.
- **M5 — full VIPR** (`rnd` + `uns` + assumption sets) → real partial-pattern leaves.
- **M6 — per-leaf + coverage** (`Coverage/Tautology`, manifest, `Pipeline/Soundness`)
  on the real `sample.aptp`.
- **M7 — Conv2d + scale** (parallel leaf checking, larger nets).
- **M8 (optional, research) — completeness**: every true property has a certificate
  (needs Mathlib Farkas / LP duality bridged to finite-dimensional ℚ).
