# VIPR checker (`viprcheck`)

Kernel-checked Lean 4 checker for **VIPR v1.0 infeasibility certificates**, in exact
rationals. This is the tool described in the companion paper in this directory
([`main.tex`](main.tex) / [`main.pdf`](main.pdf)).

The solver (exact SCIP) is **untrusted**. `viprcheck` re-reads the certificate and
replays every derivation step with `checkSem`. If it prints `ACCEPT`, theorem
`checkSem_sound` applies: no assignment that is integral on the declared integer
variables satisfies the certificate’s `CON` rows.

## Setup

Install [`elan`](https://github.com/leanprover/elan), then build from `lean_impl/`
(this directory’s parent). Toolchain: Lean 4.31.0 + Mathlib, pinned by
`lean-toolchain` and `lakefile.toml`. See also [`../README.md`](../README.md).

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"

cd /Users/haiduong/Desktop/APTPchecker/lean_impl
lake exe cache get
lake build
```

That produces `viprcheck`. SCIP is **not** required to check an existing `.vipr`.

## Run the paper example (knapsack)

The running example is the integer-infeasible knapsack
`6x+10y+15z = 23`, `x+y+z ≥ 1`, `0 ≤ x ≤ 3`, `0 ≤ y ≤ 2`, `0 ≤ z ≤ 1`, with
`x,y,z ∈ ℤ`. Its linear relaxation is feasible, so the certificate must branch.
Official exact SCIP 10.0.1 produced
[`../examples/uns_knapsack.vipr`](../examples/uns_knapsack.vipr) from
[`../examples/uns_knapsack.mps`](../examples/uns_knapsack.mps) (32 steps:
`asm`×2, `lin`×21, `rnd`×8, `uns`×1). Re-check that file:

```bash
cd /Users/haiduong/Desktop/APTPchecker/lean_impl
lake exe viprcheck examples/uns_knapsack.vipr
```

Expected: `ACCEPT`, with `vars 3  int 3  con 8  steps 32` and those reason counts.
Exit code `0` on accept, `1` on usage/parse error, `2` on reject.

Any other VIPR v1.0 `RTP infeas` file is the same command with a different path.

## Optional: regenerate the certificate

Only needed if you want SCIP to emit a fresh `.vipr` from the MPS. Requires official
SCIP **10.0.1** built with exact solving (not 9.x). Full recipe:
[`../docs/SCIP-SETUP.md`](../docs/SCIP-SETUP.md).

Run the SCIP block from `lean_impl/` as well:

```bash
cd /Users/haiduong/Desktop/APTPchecker/lean_impl
scip -c "set exact enable TRUE" \
     -c "set presolving maxrounds 0" \
     -c "set separating maxrounds 0" -c "set separating maxroundsroot 0" \
     -c "set certificate filename examples/uns_knapsack.vipr" \
     -c "read examples/uns_knapsack.mps" \
     -c "optimize" -c "quit"
```

Then run `lake exe viprcheck` on the file SCIP wrote. A different SCIP build may
emit a different (still valid) derivation; `checkSem` accepts any well-formed proof
of infeasibility, not only the checked-in one.

## What is trusted

Trusted: the Lean kernel, and the meaning of “satisfies” / “infeasible”. Not trusted:
SCIP, the `.vipr` text (the parser is verified), and this CLI’s OS/file plumbing.
A solver bug can cause a spurious `REJECT`, never a false `ACCEPT`.
