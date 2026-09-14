# LeanVIPR (`viprcheck`)

LeanVIPR is a formally verified Lean 4 checker for **VIPR v1.0 infeasibility
and objective-range certificates**, using exact rational arithmetic. The companion paper is
[`paper/main.tex`](paper/main.tex).

The solver (exact SCIP) is **untrusted**. `viprcheck` re-reads the certificate,
emits its parsed AST as Lean data, and asks Lean's kernel to prove
the relevant Boolean acceptance theorem by reduction. `RTP infeas` uses the
refutation checker; `RTP range` additionally checks every `SOL` vector, `{ sol }`
steps, the primal witness bound, and the final closed dual-bound row. It prints
`ACCEPT` only after deriving `Vipr.ClaimValid cert`.

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

## Run the paper example (knapsack)

The running example is the integer-infeasible knapsack
`6x+10y+15z = 23`, `x+y+z ≥ 1`, `0 ≤ x ≤ 3`, `0 ≤ y ≤ 2`, `0 ≤ z ≤ 1`, with
`x,y,z ∈ ℤ`. Its linear relaxation is feasible, so the certificate must branch.
Official exact SCIP 10.0.3 produced
[`examples/uns_knapsack.vipr`](examples/uns_knapsack.vipr) from
[`examples/uns_knapsack.mps`](examples/uns_knapsack.mps) (32 steps:
`asm`×2, `lin`×21, `rnd`×8, `uns`×1). Re-check that file:

```bash
lake exe viprcheck examples/uns_knapsack.vipr
```

Expected: `ACCEPT`, with `vars 3  int 3  con 8  steps 32`, those reason counts,
and a generated proof under `/tmp/viprcheck_proof/LeanVIPRGenerated/`.
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
lake exe viprcheck --kernel-mode full CERT.vipr --proof-dir /tmp/vipr-full
lake exe viprcheck --kernel-mode reconstruct CERT.vipr --proof-dir /tmp/vipr-reconstruct
```

`full` kernel-checks the complete certificate with the array-backed checker.
`reconstruct`, which is the default, backward-slices the certificate and runs
the same checker on the slice for `RTP infeas`. The kernel checks both
the sliced replay and a row-subset theorem
transporting infeasibility back to the original certificate. If slicing fails,
the command falls back to complete replay, so it does not lose acceptance
completeness. Range certificates currently use complete replay.

## Optional: regenerate the certificate

Only needed if you want SCIP to emit a fresh `.vipr` from the MPS. Requires official
SCIP **10.0.3** built with exact solving (not 9.x). Full recipe:
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

The artifact includes 20 infeasibility certificates from the published ALU
suite and 6 objective-range certificates from ALU/MIPLIB 3.0. All are genuine
official exact-SCIP 10.0.3 output.

Measured as one warmed sequential run on an Apple M3 Pro (12 cores, 36 GB),
Lean 4.31.0, macOS 26.6.2. These are compiled CLI timings and are not kernel
certification.

| Infeasibility family | Files | C++ pipeline | Lean full | Lean sliced |
|---|---:|---:|---:|---:|
| `alu4` | 6 | 0.74 s | 3.51 s | 0.80 s |
| `alu5` | 5 | 0.12 s | 0.51 s | 0.22 s |
| `alu6` | 5 | 0.48 s | 2.16 s | 0.54 s |
| `alu7` | 4 | 0.24 s | 2.31 s | 1.88 s |
| **Total** | **20** | **1.58 s** | **8.49 s** | **3.44 s** |

Range certificates currently use complete replay:

| Certificate | Steps | C++ pipeline | Lean full |
|---|---:|---:|---:|
| `alu4_9` | 40,648 | 0.14 s | 2.96 s |
| `egout` | 372 | 0.05 s | 0.09 s |
| `enigma` | 36,872 | 0.26 s | 13.72 s |
| `flugpl` | 7,553 | 0.09 s | 0.19 s |
| `gt2` | 3,284 | 0.21 s | 2.80 s |
| `vpm1` | 6,416 | 0.62 s | 8.65 s |
| **Total** | **95,145** | **1.37 s** | **28.41 s** |

The C++ column is the official `viprcomp --soplex=off --threads=1` followed by
`viprchk`, because every selected solver certificate contains `lin weak`.
No false acceptance was observed from the complete pipeline.

The exact per-certificate measurements and structural counts are in
[`benchmarks/results/checker.csv`](benchmarks/results/checker.csv);
official
C++ pipeline measurements are in
[`benchmarks/results/cpp.csv`](benchmarks/results/cpp.csv). Reproduce the Lean
measurements with:

```bash
python3 benchmarks/run_compiled.py \
  --modes full slice \
  --output benchmarks/results/checker.csv
```
