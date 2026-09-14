# Agent handoff: LeanVIPR submission branch

Date: 2026-09-14  
Repository: `/Users/crusong/Documents/aptpchecker`  
Branch: `vipr-submission`

## Immediate user intent

1. A fully implemented and verified array-backed checker now exists:
   - `LeanVIPR/Cert/ViprChecker.lean`
   - direct soundness proof: `LeanVIPR/Cert/ViprCheckerSound.lean`
   - array-backed replay pool rather than repeated list append;
   - fused validation/replay and final-entry inspection;
   - one `scomb` computation per `lin`/`rnd` check;
   - supports both `RTP infeas` and `RTP range`, including `sol`.
   - production CLI modes: `full` and `slice`; both execute this checker.
   - `checkVipr_refines` proves Boolean acceptance implies declarative
     VIPR certificate validity.
   - `checkVipr_sound` proves claim soundness directly.
   - `#print axioms` reports only `propext`, `Classical.choice`, and
     `Quot.sound`.

2. The implementation has been tested after the proof-friendly replay
   refactor:
   - all 46 optimized timing invocations pass;
   - measurements are in `benchmarks/results/checker.csv`.

3. The verified array-backed checker is the only executable checker and is the
   native and kernel entry point. The list replay that remains in
   `ViprSem.lean` is declarative proof-system semantics, not a second checker.

4. Benchmark presentation has been corrected:
   - `C++ ok` / yes-no acceptance columns were removed from the paper and README.
   - The tables retain only official C++ pipeline timing.
   - The wording states that no false acceptance was observed from the complete
     pipeline.

5. The earlier requested official `viprchk` soundness audit remains pending:
   - Seek a certificate that `viprchk` accepts although the claimed MILP result is
     false.
   - Use malformed and adversarial edge cases, not merely the existing valid
     benchmarks.
   - Differentially check candidates with the Lean checker whenever both parsers
     support the input.
   - Distinguish false acceptance from crashes, false rejection, parser limitations,
     and `viprcomp` defects.

## Current conceptual conclusion

- `viprcomp` is a certificate completer, not the final verifier.
- The intended official path for these solver files is:

  ```text
  raw certificate containing lin weak
      -> viprcomp --soplex=off --threads=1
      -> completed certificate
      -> viprchk
  ```

- On 13 of 26 benchmark inputs, `viprcomp` exits successfully but emits a completed
  file that `viprchk` rejects.
- Example: `alu4_2`, row `AggrRow_1293`.
  `completeWeakDomination` returns failure, but `completelin` does not propagate its
  `retval`; `processDER` still returns success.
- This is a `viprcomp` completion/error-propagation defect. It is **not** evidence of
  a false acceptance by `viprchk`; the final checker rejects the invalid output.
- No genuine `viprchk` soundness counterexample has yet been established.
- An earlier suspicion that C++ unsplitting drops one branch’s residual assumptions
  was incorrect. `canUnsplit` unions both residual assumption sets.

## Benchmark corpus and measurements

The checked-in corpus under `benchmarks/` now contains real exact-SCIP output:

- 20 ALU infeasibility certificates.
- 6 ALU/MIPLIB 3.0 objective-range certificates.
- 26 MPS/VIPR pairs, manifest, and SHA-256 checksums.
- The old synthetic corpora were moved to:
  - `/private/tmp/vipr-synthetic-infeas-backup-20260913-1608`
  - `/private/tmp/vipr-synthetic-range-backup-20260913-1608`

Lean compiled measurements:

- CSV: `benchmarks/results/checker.csv`
- Runner: `benchmarks/run_compiled.py`
- 46/46 invocations pass.
- Infeasibility full replay: 8.49 s.
- Infeasibility sliced replay: 3.44 s.
- Range full replay total: 28.41 s.

Official C++ measurements:

- CSV: `benchmarks/results/cpp.csv`
- Runner: `benchmarks/run_cpp.py`
- Source commit: `30f2951d1e90e47afa821bdd1b12b82246656c42`
- C++ pipeline totals, including time to final rejection:
  - Infeasibility: 1.58 s.
  - Range: 1.37 s.
- Final `viprchk` outcomes:
  - Infeasibility: 8 accept, 12 reject.
  - Range: 5 accept, 1 reject.
- These outcome counts should not remain as a “C++ ok” metric per the latest user
  instruction.

## Current paper/README state

`paper/main.tex` and `README.md` now show C++ pipeline timing without `C++ ok`
columns or acceptance counts. The PDF must be rerendered after this correction:

```bash
cd paper
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Use `-g`; ordinary `latexmk` previously reused a stale PDF because of timestamps.
Render pages 9 and 10 with Ghostscript to inspect the tables, then open the PDF because
the user previously requested every paper edit be rerendered and opened.

## Official C++ checkout and binaries

Local upstream checkout:

```text
/private/tmp/vipr-upstream-audit
```

Built binaries:

```text
/private/tmp/vipr-upstream-audit/build-cmake/viprcomp
/private/tmp/vipr-upstream-audit/build-cmake/viprchk
```

Installed during this work:

- SoPlex 8.0.3 via Homebrew.
- CMake 4.4.3 via Homebrew.

Representative pipeline command:

```bash
/private/tmp/vipr-upstream-audit/build-cmake/viprcomp \
  --soplex=off --threads=1 \
  --outfile=/private/tmp/example_complete.vipr \
  benchmarks/infeas/alu4_2.vipr

/private/tmp/vipr-upstream-audit/build-cmake/viprchk \
  /private/tmp/example_complete.vipr
```

## Pending `viprchk` soundness audit

Useful existing adversarial files:

```text
/private/tmp/vipr-checker-review/forged1.vipr
/private/tmp/vipr-checker-review/forged2.vipr
/private/tmp/vipr-checker-review/manipulated1.vipr
```

They have not yet been systematically rerun against both current binaries and the Lean
checker. `forged1.vipr` and `forged2.vipr` target objective-range/SOL handling;
`manipulated1.vipr` targets assumptions/reference hierarchy.

Source-audit leads in `code/viprchk.cpp`:

- `readMultipliers` checks negative indices unconditionally, but the upper-bound check
  is inside `#ifndef NDEBUG`. Release builds may therefore perform an out-of-range
  vector access on a malformed reference. This is at least a robustness issue; do not
  call it a soundness bug without a false-accepting certificate.
- `canUnsplit` warns rather than fails when the supplied branch assumption is absent.
  Analyze whether this can remove all real dependencies; initial reasoning suggests
  residual assumptions remain, so no exploit is established.
- Inspect `SOL`, range acceptance, empty derivations, objective sense/integrality,
  duplicate multiplier indices, constraint labels/indexing, hierarchy/trashing, and
  final-assumption checks.

The desired result is an evidence table such as:

| Attack class | C++ result | Lean result | Classification |
|---|---|---|---|
| forged false range | ... | ... | false acceptance / rejected |
| invalid reference | ... | ... | crash / clean reject |
| malformed unsplit | ... | ... | ... |

Only label a case a soundness bug when `viprchk` returns success for a mathematically
false claim.

## Working tree

The branch is intentionally dirty and uncommitted/unpushed. Existing user changes must
be preserved. Current status includes modified Lean, paper, README, and manual files,
plus the untracked `benchmarks/` directory.

Run before handoff completion:

```bash
git diff --check
git status --short
```

Do not commit or push unless the user explicitly asks.
