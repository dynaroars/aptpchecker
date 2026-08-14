# Project status, in plain English

## Bottom line

This project rebuilds, in the Lean 4 proof language, a tool that double-checks
proofs that a neural network satisfies a property. Instead of trusting an
outside solver, it re-checks that solver's evidence using exact fraction
arithmetic (no floating-point rounding). The tool runs end to end: it parses the
network and proof, turns each branch into equations with a **verified** encoder,
has exact SCIP prove each branch, and re-checks SCIP's certificate with a
machine-checked checker. Every heavy step — the parsers, the encoder, the
certificate checker, and the coverage argument — is machine-verified and
axiom-clean, and crucially the encoder that runs is the same one that's proven.
Those pieces are now bolted together into a **single theorem**, `certify_network_sound`:
if coverage holds and every leaf's `leafCheck` passes, then the network satisfies the
property on the whole input box. `leafCheck` is the per-leaf check the tool actually runs
— the verified certificate checker **plus** a certificate↔encoding correspondence check
(the certificate's constraints really are this leaf's encoded equations) plus an
integer-variable check. So when the tool prints CERTIFIED it has computed exactly this
theorem's hypothesis. What remains trusted: the OS/file I/O and process plumbing (reading
the files, invoking SCIP, and `main` faithfully AND-ing the per-leaf checks); SCIP itself
stays untrusted (re-checked); and the step that maps SCIP's renumbered certificate
variables back to encoder ids is untrusted-but-harmless (a wrong map only causes a
spurious rejection, never a false CERTIFIED).

## What's proven (in plain terms)

Each item below is *machine-verified* — checked by Lean's proof kernel using only
its three standard foundational assumptions, with no shortcuts and no reliance on
compiled code.

- **The core "no counterexample" math.** The logical rule the checker leans on to
  turn a solver's evidence into a genuine "this region contains no
  counterexample" is proven.
- **Coverage.** The proof that the pieces of the search ("leaves") together cover
  the entire input range — nothing is skipped — is proven.
- **The network-to-equations translation, for standard networks.** Turning the
  network plus its input range into the exact system of inequalities that the
  solver reasons about is proven correct for standard multi-layer
  fully-connected ReLU networks of any depth that end in a linear scoring layer
  (see caveats for exactly what "standard" covers). Getting this translation right
  is the central and hardest result.
- **Re-checking the solver's certificate — complete and automatic.** The full
  proof-by-cases checker (all three step kinds: add, round, and case-split) is proven
  correct and runs as a `Bool` function; it connects to the certificate-file parser,
  so a validated refutation of a certificate's constraints proves them infeasible.
  Verified running on a small example that genuinely needs a case-split.
- **The end-to-end argument.** The top-level reasoning that combines coverage and
  per-piece refutation into the final guarantee is proven.
- **Both input-file readers.** The parser for the exact-network file *and* the
  parser for the proof-tree file are both fully verified (each proven to be the
  exact inverse of a printer), so neither has to be trusted anymore.

The exact-arithmetic groundwork is also cross-checked against an independent
implementation and matches exactly, and the input-file readers reproduce the
original Python tool's output on the sample files.

## What's NOT covered yet / caveats

- **The command-line tool (`aptpcheck`) is now assembled and runs end-to-end.**
  It parses the network and proof tree, verifies coverage, encodes each leaf to
  VIPR, invokes exact SCIP, then re-checks the certificate with the fully-verified
  `checkVipr`. There is no untrusted converter on the checking path: the flat
  certificate is read directly by the verified checker (which re-does all the math
  itself). What's needed to *use* it in practice: an installed exact SCIP binary
  (SoPlex-backed); without it, the tool can only report that it cannot reach the
  solver.

- **Only standard fully-connected ReLU networks are covered.** The proof applies
  to a "normal form" network: a first linear layer followed by any number of
  ReLU-then-linear blocks, finishing with a linear scoring layer. Two
  simplifications are baked in and lose no generality for this kind of network:
  a "flatten" step (reshaping data) is treated as doing nothing, and back-to-back
  linear layers (or back-to-back ReLUs) are merged. **Convolutional networks
  (CNNs) are not covered yet** — that is planned future work.

- **The command-line tool (`aptpcheck`) is assembled.** It handles all three
  solver-certificate step kinds (add, round, case-split) in a single verified flat
  checker. The only external dependency at runtime is an exact SCIP installation.

Nothing outstanding requires trusting the external solver or any floating-point
arithmetic — those stay outside the trusted core by design.

## What you can run today

The end-to-end tool works. With official exact SCIP installed (see
`docs/SCIP-SETUP.md`), running

```
APTP_SCIP=/path/to/scip aptpcheck examples/sample.net examples/sample.aptp
```

parses both files, verifies coverage, encodes each leaf as an exact-rational MILP with
the **verified** leaf-aware encoder, calls exact SCIP to produce a proof certificate, and
re-checks every certificate with the kernel-checked checker. On the sample it reports
**CERTIFIED** — all four leaves' real SCIP certificates are accepted by the verified
checker.

There is now **one** encoder, and it is the one that is both run and proven: `encFold`
(leaf-aware — it folds sign-fixed neurons and only puts a big-M switch on genuinely
unstable ones). Its soundness (`encFold_overapprox`, and `certified_sound_network_fold`
which transports it onto the parsed network) is machine-checked and axiom-clean, and the
CLI feeds SCIP exactly these rows. The old uniform encoder and the separate unverified
encoder have both been deleted, so the earlier "encoder-vs-model" gap is closed: the
equations SCIP sees are the equations the soundness theorem is about.

The checker also handles **branching**: when SCIP does its own case-split on a 0/1
variable inside a leaf (an `uns` step), the checker validates the split — the two
discharged bounds must be complementary integer bounds, each branch's row must dominate
the stated row — and its soundness is part of the same machine-checked proof. This is
validated on a *real* branched certificate from official SCIP (an integer-infeasible
knapsack SCIP solved with 3 branch-and-bound nodes; `examples/uns_knapsack.vipr`), which
the checker accepts — and correctly rejects when the integrality declaration is removed
or the certificate is truncated.
