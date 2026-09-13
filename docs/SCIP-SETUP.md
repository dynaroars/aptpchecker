# Exact SCIP setup + real-certificate findings

## Which SCIP

Exact **rational** solving with **VIPR certificate output** was upstreamed into
**official SCIP 10** (files `certificate.cpp`, `lpexact.c`, `cons_exactlinear.c`, …).
It is *not* in the 9.2.0 release, nor in older mainline. Use the official
`scipoptsuite-10.0.1` (from scipopt.org). (A separate unofficial fork,
`leoneifler/exact-SCIP`, also exists but we do not use it.)

## Build recipe (arm64 macOS, verified working)

```
brew install boost mpfr gmp           # gmp usually already present
curl -sLO https://www.scipopt.org/download/release/scipoptsuite-10.0.1.tgz
tar xzf scipoptsuite-10.0.1.tgz && cd scipoptsuite-10.0.1
mkdir build && cd build
cmake .. \
  -DCMAKE_PREFIX_PATH=/opt/homebrew \
  -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
  -DEXACTSOLVE=ON -DGMP=on -DMPFR=on -DBOOST=on \
  -DZIMPL=off -DPAPILO=off -DGCG=off -DUG=off -DIPOPT=off -DSYM=none \
  -DREADLINE=off -DZLIB=off -DAMPL=off -DCMAKE_BUILD_TYPE=Release
make -j8 scip
# binary: build/bin/scip   (reports: "support for exact solving mode using exact LP solver SoPlex")
```

ZIMPL/PaPILO are disabled (system Bison is too old for ZIMPL; PaPILO pulls a
FetchContent sub-build that fails). Neither is needed: we feed MPS and disable
presolving (presolving is not certified anyway).

## Invocation (exact solve + complete certificate)

```
scip -c "set exact enable TRUE" \
     -c "set presolving maxrounds 0" \
     -c "set separating maxrounds 0" -c "set separating maxroundsroot 0" \
     -c "set certificate filename OUT.vipr" \
     -c "read PROBLEM.mps" -c "optimize" -c "quit"
```

The exact MPS reader parses coefficients via `RatSetString`, which accepts exact
`num/den` fractions — so we can emit our exact-ℚ encoding losslessly (dyadic or not).

## Real certificate observed (infeasible `2x≤1 ∧ 2x≥1`, x integer)

Official SCIP 10 emits (abridged): CON C0/C1 + variable bounds B2/B3; then DER with
signed-multiplier `lin` steps and `rnd` cuts, ending in `ActivityConflict11 L -1 0
{ lin 2 1 -1 6 2 }` — i.e. `-1·(2x≥1) + 2·(x≤0) ⇒ 0 ≤ -1`. (No case-split needed here;
SCIP used Gomory rounding.)

## Checker support

The checker implements the VIPR v1.0 rules used by official exact SCIP:

- signed suitable combinations over mixed `L`, `G`, and `E` senses;
- domination of the stated row;
- integer rounding;
- assumption introduction and branch discharge with `uns`;
- `RTP infeas` and finite `RTP range` results, including `SOL` and `{ sol }`.

The checked-in knapsack certificate was emitted by official exact SCIP 10.0.1
and exercises `asm`, `lin`, `rnd`, and `uns`.
