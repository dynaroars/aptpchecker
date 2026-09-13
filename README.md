# VIPR checker (`viprcheck`)

Kernel-checked Lean 4 checker for **VIPR v1.0 infeasibility and objective-range
certificates**, using exact rational arithmetic. The companion paper is
[`paper/main.tex`](paper/main.tex).

The solver (exact SCIP) is **untrusted**. `viprcheck` re-reads the certificate,
emits its parsed AST as Lean data, and asks Lean's kernel to prove
the relevant Boolean acceptance theorem by reduction. `RTP infeas` uses the
refutation checker; `RTP range` additionally checks every `SOL` vector, `{ sol }`
steps, the primal witness bound, and the final closed dual-bound row. It prints
`ACCEPT` only after deriving either infeasibility or `ResultCorrect cert`.

## Setup

Install [`elan`](https://github.com/leanprover/elan), then build from this
directory. Lean 4.31.0 and Mathlib are pinned by `lean-toolchain` and
`lakefile.toml`.

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"

lake exe cache get
lake build
```

That produces `viprcheck`. SCIP is **not** required to check an existing `.vipr`.

## Developer audit manual

The anonymous developer manual maps the executable checker to its declarative
proof system, main soundness theorems, termination and structural-cost results,
kernel-replay path, and remaining trust boundaries. Build its multi-page HTML:

```bash
lake exe viprcheck-manual --output manual/_out
```

Serve the generated site locally:

```bash
python3 -m http.server 8000 --directory manual/_out/html-multi
```

The source is [`manual/ViprCheckManual.lean`](manual/ViprCheckManual.lean).

## Run the paper example (knapsack)

The running example is the integer-infeasible knapsack
`6x+10y+15z = 23`, `x+y+z ≥ 1`, `0 ≤ x ≤ 3`, `0 ≤ y ≤ 2`, `0 ≤ z ≤ 1`, with
`x,y,z ∈ ℤ`. Its linear relaxation is feasible, so the certificate must branch.
Official exact SCIP 10.0.1 produced
[`examples/uns_knapsack.vipr`](examples/uns_knapsack.vipr) from
[`examples/uns_knapsack.mps`](examples/uns_knapsack.mps) (32 steps:
`asm`×2, `lin`×21, `rnd`×8, `uns`×1). Re-check that file:

```bash
lake exe viprcheck examples/uns_knapsack.vipr
```

Expected: `ACCEPT`, with `vars 3  int 3  con 8  steps 32`, those reason counts,
and a generated proof under `/tmp/viprcheck_proof/ViprCheckGenerated/`.
Exit code `0` on accept, `1` on usage/parse error, `2` on reject.

Any other VIPR v1.0 `RTP infeas` file is the same command with a different path.
Use `--proof-dir DIR` to retain a separate generated artifact:

```bash
lake exe viprcheck examples/uns_knapsack.vipr --proof-dir /tmp/vipr-knapsack
```

Two small range examples exercise minimization and maximization, including
`{ sol }`:

```bash
lake exe viprcheck examples/valid_min_range.vipr
lake exe viprcheck examples/valid_max_range.vipr
```

For performance comparison only, the explicitly untrusted compiled path is:

```bash
lake exe viprcheck --native-precheck examples/uns_knapsack.vipr
```

It never claims kernel certification.

The two kernel modes are:

```bash
lake exe viprcheck --kernel-mode list CERT.vipr --proof-dir /tmp/vipr-list
lake exe viprcheck --kernel-mode reconstruct CERT.vipr --proof-dir /tmp/vipr-reconstruct
```

`list` kernel-checks the complete original list replay. `reconstruct`, which is
the default, backward-slices the certificate and runs the same list checker on
the slice for `RTP infeas`. The kernel checks both the sliced replay and a row-subset theorem
transporting infeasibility back to the original certificate. If slicing fails,
the command falls back to complete list replay, so it does not lose acceptance
completeness. Range certificates currently use complete list replay.

## Optional: regenerate the certificate

Only needed if you want SCIP to emit a fresh `.vipr` from the MPS. Requires official
SCIP **10.0.1** built with exact solving (not 9.x). Full recipe:
[`docs/SCIP-SETUP.md`](docs/SCIP-SETUP.md).

Run the SCIP block from the repository root:

```bash
scip -c "set exact enable TRUE" \
     -c "set presolving maxrounds 0" \
     -c "set separating maxrounds 0" -c "set separating maxroundsroot 0" \
     -c "set certificate filename examples/uns_knapsack.vipr" \
     -c "read examples/uns_knapsack.mps" \
     -c "optimize" -c "quit"
```

Then run `lake exe viprcheck` on the file SCIP wrote. A different SCIP build may
emit a different (still valid) derivation; the result checker accepts any
well-formed supported VIPR derivation, not only the checked-in examples.

## What is trusted

Relative to the emitted certificate AST, trusted: the Lean kernel and the small
definitions of “satisfies” and “infeasible”. Not trusted: SCIP, certificate replay
in the compiled CLI, and proof generation. The generated theorem is checked with
`decide +kernel`, not `native_decide`.

The current artifact does not kernel-check that the emitted AST is the parse of the
exact source bytes. Therefore the parser/compiler/runtime and OS/file plumbing remain
a frontend trust boundary for that binding. Parser verification is intentionally
deferred; it is not included in the certificate-replay benchmark below.

## VIPR-only benchmark

The table below is the pre-finite-set performance baseline. The current checker
deduplicates open assumptions and has a verified quadratic structural bound;
the complete five-certificate timing suite should be rerun before publication
once the four NN-leaf input files are restored alongside the repository. As a
post-refactor smoke measurement, directly rechecking the generated knapsack
`Proof.lean` took 23.18 s for complete replay and 21.12 s for reconstruction;
end-to-end CLI timings on the same host showed substantial process/file-system
wall-time variance and are not substituted into the table.

Measured as single warmed sequential runs on an Apple M3 Pro (12 cores, 36 GB),
Lean 4.31.0, macOS 26.6.2. The compiled column is complete
`--native-precheck` wall time and is not kernel certification. Each kernel
number includes emitting `Data.lean` and kernel-checking `Proof.lean`. No
problem generation or SCIP execution is included.

| Certificate | Size | Steps | Compiled CLI | Complete list replay | List reconstruction |
|---|---:|---:|---:|---:|---:|
| `uns_knapsack.vipr` | 1.99 KiB | 32 | 0.04 s | 22.98 s | 22.61 s |
| NN leaf `[-4]` | 7.54 KiB | 97 | 0.04 s | 28.62 s | 24.10 s |
| NN leaf `[-2,4]` | 22.43 KiB | 273 | 0.05 s | 28.13 s | 24.99 s |
| NN leaf `[2,1,4]` | 16.13 KiB | 177 | 0.04 s | 25.02 s | 24.71 s |
| NN leaf `[2,-1,4]` | 82.05 KiB | 983 | 0.07 s | 181.81 s | 39.67 s |
| **Total, all five** | **130.14 KiB** | **1,562** | **0.24 s** | **286.56 s** | **136.08 s** |

List reconstruction is 2.11× faster than complete list replay over the full
suite, reducing wall time by 52.51%. The checked slices are:

| Certificate | Constraints | Derivation steps |
|---|---:|---:|
| knapsack | 8→7 | 32→23 |
| NN leaf `[-4]` | 38→8 | 97→13 |
| NN leaf `[-2,4]` | 35→17 | 273→72 |
| NN leaf `[2,1,4]` | 32→12 | 177→11 |
| NN leaf `[2,-1,4]` | 32→18 | 983→281 |

Exact benchmark inputs (SHA-256):

```text
813481425ded676a3b97eaf166bedf0768c169fab99d47cdeb729a640419bdfb  examples/uns_knapsack.vipr
3dc36e50026f8f57ac9334b6597c4f26f07fbf0a578f358db98799d5ab31b006  leaf_0.vipr
a1fd93aea9165224c4930d87a7f3340a61dab502a7bf887a1a84eeb73938d20e  leaf_1.vipr
7ba53d47e7c95a47a6d51333f64888f637245a83822a472f4ba4bc70e36b6424  leaf_2.vipr
94351df62742f09545aea71cd8a970b9afe2451fe1cc47e08d53f6ad4368e1c7  leaf_3.vipr
```
