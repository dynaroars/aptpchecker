import VersoManual
import LeanVIPR

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "LeanVIPR Developer Audit Manual" =>
%%%
authors := ["Anonymous"]
shortTitle := "LeanVIPR Audit"
%%%

This manual is the developer-facing audit guide for the anonymous LeanVIPR artifact.
It explains what the checker accepts, how the executable path reaches a
kernel-checked theorem, where the main mathematical arguments live, and what
remains trusted.
It is not a replacement for the paper's mathematical presentation.
Its purpose is to make an independent source audit reproducible.

# Audit contract
%%%
tag := "audit-contract"
%%%

The artifact checks VIPR v1.0 result certificates over exact rational data.
There are two accepted result shapes:

* `RTP infeas` certificates derive a closed contradiction from the certificate's
  `CON` rows and declared integer variables.
* `RTP range` certificates additionally validate solution vectors, `{ sol }`
  steps, objective bounds, and the final result row.

The primary claim is _soundness_, not search completeness:

* if the infeasibility checker returns `true`, the represented mixed-integer
  system has no real valuation satisfying the rational rows and declared
  integrality conditions;
* if the full result checker returns `true`, the declarative result predicate for
  the parsed certificate holds.

The checker does not claim that every infeasible MILP has a certificate accepted
by this implementation.
The exact completeness boundary is documented in
{ref "completeness-boundary"}[Completeness boundary].

# Quick start
%%%
tag := "quick-start"
%%%

Build the checker and this manual from the repository root:

```
lake exe cache get
lake build
lake exe viprcheck-manual --output manual/_out
```

Serve the generated multi-page manual:

```
python3 -m http.server 8000 --directory manual/_out/html-multi
```

Check the included infeasibility certificate with kernel reconstruction:

```
lake exe viprcheck examples/uns_knapsack.vipr \
  --proof-dir /tmp/vipr-knapsack
```

Check the two small objective-range certificates:

```
lake exe viprcheck examples/valid_min_range.vipr
lake exe viprcheck examples/valid_max_range.vipr
```

An accepted run exits with code `0` and reports the generated theorem
`LeanVIPR.Generated.certified`.
A usage or parse error exits with code `1`; rejection or failed kernel checking
exits with code `2`.

# Source map
%%%
tag := "source-map"
%%%

An audit can proceed in the following order:

1. `LeanVIPR/Ast/Number.lean` and `LeanVIPR/Ast/Vipr.lean`
   define exact numbers, the parsed certificate syntax, and conversion of
   `CON` rows.
2. `LeanVIPR/Cert/LinCon.lean` defines sparse rational linear forms,
   satisfaction, and the Farkas core.
3. `LeanVIPR/Cert/Vipr.lean` proves the elementary linear-combination,
   rounding, and integer-split lemmas.
4. `LeanVIPR/Cert/ViprSem.lean` defines sensed constraints, primitive rule
   checks, assumption sets, and the declarative list replay.
5. `LeanVIPR/Cert/ViprSystemSound.lean` defines the declarative proof system
   over real-valued MILP semantics and proves proof-system soundness.
6. `LeanVIPR/Cert/ViprRuleSound.lean` proves that the executable Boolean rule
   checks refine the declarative rules.
7. `LeanVIPR/Pipeline/Vipr.lean` converts parsed records to replay steps and
   resolves v1.0 certificate rows.
8. `LeanVIPR/Cert/ViprClaimSound.lean` extends replay to `RTP range`,
   solution records, and objective correctness.
9. `LeanVIPR/Cert/ViprChecker.lean` contains the sole executable checker, while
   `LeanVIPR/Cert/ViprCheckerSound.lean` proves it directly sound.
10. `LeanVIPR/Cert/ViprTermination.lean` and
   `LeanVIPR/Cert/ViprComplexity.lean` state termination and structural-cost
   results.
11. `LeanVIPRMain.lean` is the untrusted command-line and proof-artifact generator.

# Data and semantics
%%%
tag := "data-semantics"
%%%

Certificate coefficients and right-hand sides are represented by Lean's exact
rational type `ℚ`.
A sparse linear form is a list of variable indices and rational coefficients.
The proof-system semantics nevertheless use real-valued assignments, matching
standard MILP semantics.
Integer-declared coordinates must be casts of integers.

The core semantic definitions are:

* {name}`LeanVIPR.Cert.ViprSystem.RealValuation` for assignments into `ℝ`;
* {name}`LeanVIPR.Cert.ViprSystem.evalReal` for evaluating a rational form in
  such an assignment;
* {name}`LeanVIPR.Cert.ViprSystem.satReal` for satisfying a sensed row;
* {name}`LeanVIPR.Cert.ViprSystem.IsIntReal` for the declared integrality
  condition.

Keeping certificate data rational makes parsing, normalization, and checker
evaluation computable.
Casting those coefficients into `ℝ` in the declarative layer makes the final
infeasibility theorem a statement about the intended real MILP semantics, rather
than only about rational test assignments.

# VIPR proof rules
%%%
tag := "proof-rules"
%%%

## Linear combination: `lin`
%%%
tag := "rule-lin"
%%%

A `lin` step references earlier rows with rational multipliers.
The signs of the multipliers must be suitable for the senses of the referenced
rows.
After combination, the stated row must either match the combined form and be no
stronger than its bound, or directly be an absurd zero row.

The declarative rule is {name}`LeanVIPR.Cert.ViprSystem.LinValid`.
Its semantic theorem is
{name}`LeanVIPR.Cert.ViprSystem.linValid_sound`: a declaratively valid linear
combination preserves satisfaction over every real valuation.

The executable check is {name}`LeanVIPR.Cert.linCheck`.
The Boolean-to-declarative refinement theorem is
{name}`LeanVIPR.Cert.ViprRule.linCheck_valid_real`.

## Integer rounding: `rnd`
%%%
tag := "rule-rnd"
%%%

A `rnd` step first forms a suitable linear combination.
The checker establishes that the resulting linear form is integer-valued under
the declared integrality conditions, then validates the appropriate rounded
bound.

The declarative rule and its semantic theorem are
{name}`LeanVIPR.Cert.ViprSystem.RndValid` and
{name}`LeanVIPR.Cert.ViprSystem.rndValid_sound`.
The Boolean refinement is
{name}`LeanVIPR.Cert.ViprRule.rndCheck_valid_real`.

## Assumptions and unsplitting: `asm` and `uns`
%%%
tag := "rule-uns"
%%%

An `asm` step records a temporary branch row in the pool and in that entry's
finite set of open assumptions.
An `uns` step references two derived rows whose assumptions differ by
complementary integer bounds.
It checks that the bounds exhaust all integer values, discharges those two branch
assumptions, and retains all other open assumptions.

The declarative split condition is
{name}`LeanVIPR.Cert.ViprSystem.ComplementaryBounds`.
The executable split check is {name}`LeanVIPR.Cert.unsBoundsB`, refined by
{name}`LeanVIPR.Cert.ViprRule.unsBoundsB_valid_real`.

## Solution steps and range results
%%%
tag := "rule-sol"
%%%

For `RTP range`, the checker validates every listed sparse solution against the
original rows and integrality declarations.
A `{ sol }` derivation row is accepted only when it is justified by a listed
solution's objective value.
The final certificate must provide the required closed contradiction or a closed
row that dominates the claimed objective bound.

The declarative certificate predicate is
{name}`LeanVIPR.Ast.Vipr.ProofValid`.
The user-facing semantic result is
{name}`LeanVIPR.Ast.Vipr.ClaimValid`.

# Theorem hierarchy
%%%
tag := "theorem-hierarchy"
%%%

The implementation deliberately separates mathematical proof-system soundness
from correctness of the Boolean recognizer.
This creates two independently auditable layers.

## Declarative proof-system soundness
%%%
tag := "proof-system-soundness"
%%%

{name}`LeanVIPR.Cert.ViprSystem.StepValid`,
{name}`LeanVIPR.Cert.ViprSystem.DerivationValid`, and
{name}`LeanVIPR.Cert.ViprSystem.ProofValid` are propositions.
They do not call the executable Boolean checks.

The replay invariant is:

{docstring LeanVIPR.Cert.ViprSystem.replay_sound}

The main declarative infeasibility theorem is:

{docstring LeanVIPR.Cert.ViprSystem.proofSystem_sound}

For full result certificates, the corresponding theorem is:

{docstring LeanVIPR.Ast.Vipr.proofSystem_sound}

## Executable-checker refinement
%%%
tag := "checker-refinement"
%%%

The production checker uses an array-backed replay pool. Primitive Boolean rule
checks refine the declarative rules, and the complete replay refines the
declarative result certificate:

{docstring LeanVIPR.Cert.ViprChecker.stepValidB_sound}

{docstring LeanVIPR.Cert.ViprChecker.checkVipr_refines}

The user-facing semantic theorem is proved directly from that refinement:

{docstring LeanVIPR.Cert.ViprChecker.checkVipr_sound}

The high-level dependency chain is therefore:

```
rule semantics
  -> declarative replay invariant
  -> proof-system soundness

Boolean rule checks
  -> checker refinement
  -> parsed-certificate soundness
```

# Kernel-checked command-line path
%%%
tag := "kernel-path"
%%%

The normal command-line path performs the following operations:

1. Read and parse the `.vipr` file.
2. Run a compiled precheck to reject obvious failures early.
3. Emit the parsed certificate as a Lean definition in `Data.lean`.
4. Emit `Proof.lean`, containing a theorem such as
   `checkVipr cert = true := by decide +kernel`.
5. Invoke Lean on both generated modules.
6. Print `ACCEPT` only when the generated theorem and its soundness consequence
   pass kernel checking.

Both result kinds apply
{name}`LeanVIPR.Cert.ViprChecker.checkVipr_sound`.

The command:

```
lake exe viprcheck --native-precheck CERT.vipr
```

is explicitly not a certified run.
It executes the Boolean checker as compiled code and reports only a machine
Boolean.
It is useful for timing and preflight rejection, but its positive result should
not be reported as kernel certification.

# Complete replay and reconstruction
%%%
tag := "reconstruction"
%%%

The `full` mode kernel-reduces the array-backed checker over the complete certificate:

```
lake exe viprcheck --kernel-mode full CERT.vipr \
  --proof-dir /tmp/vipr-full
```

The default `reconstruct` mode backward-slices an infeasibility certificate:

```
lake exe viprcheck --kernel-mode reconstruct CERT.vipr \
  --proof-dir /tmp/vipr-reconstruct
```

Slicing and source generation are untrusted optimizations.
The generated proof independently asks the kernel to establish:

* equality of the sliced and original integer-variable declarations;
* inclusion of every retained base row in the original base rows;
* acceptance of the sliced replay.

It then applies
{name}`LeanVIPR.Cert.ViprChecker.checkViprInfeasibleSubset_sound` to transport
infeasibility back to the original parsed certificate.
If slicing does not produce an accepted replay, the command falls back to
complete replay.
Range certificates currently use complete replay.

# Termination and structural cost
%%%
tag := "termination-cost"
%%%

All recursive checker definitions are accepted by Lean's totality checker.
The explicit replay-size theorem states that one pool entry is appended per
derivation record:

{docstring LeanVIPR.Cert.ViprTermination.replaySteps_size}

A fuel presentation demonstrates that exactly one unit of derivation fuel per
step suffices:

{docstring LeanVIPR.Cert.ViprTermination.replayFuel_complete}

The observable totality theorem for parsing and checking finite text is:

{docstring LeanVIPR.Cert.ViprTermination.parseAndCheckVipr_terminates}

The implementation's structural-cost model is a vector, rather than a misleading
single unit-cost count.
It separately records rule checks, array writes, assumption storage and merges,
rule inputs, and solution inputs.
The main bound is:

{docstring LeanVIPR.Cert.ViprComplexity.checkVipr_structural_cost}

This is an algorithmic structural bound.
It does not assign constant cost to arbitrary-precision rational arithmetic, Lean
kernel reduction, process startup, or file-system operations.

# Completeness boundary
%%%
tag := "completeness-boundary"
%%%

The artifact does not claim a fully formalized completeness theorem for arbitrary
mixed-integer VIPR refutations.
It proves that an explicit exact rational Farkas witness can be represented as a
one-step closed VIPR certificate:

{docstring LeanVIPR.Cert.ViprCompleteness.farkasWitness_to_vipr}

Completeness of the rational LP fragment is then conditional on the mathematical
existence of rational Farkas witnesses:

{docstring LeanVIPR.Cert.ViprCompleteness.lpFragment_complete_of_farkas}

The remaining full mixed-integer existence statement is deliberately exposed as
{name}`LeanVIPR.Cert.ViprCompleteness.FiniteBranchAndCutComplete`, a proposition,
not a theorem proved by this development.

# Trust boundary
%%%
tag := "trust-boundary"
%%%

Relative to the emitted certificate AST, an accepted kernel run relies on:

* the Lean kernel and the logical foundations imported through Lean and Mathlib;
* the definitions that give meaning to linear-row satisfaction, integrality, and
  result correctness;
* the generated concrete certificate definition and theorem statement.

The following components may be wrong without invalidating a successfully checked
proof term:

* SCIP and all certificate search;
* the native Boolean precheck;
* backward slicing and generated-source construction;
* benchmark and reporting code.

One important frontend gap remains.
The generated proof certifies the emitted certificate AST, but the current
artifact does not prove inside Lean that this AST is exactly the parse of the
submitted source bytes.
Therefore parser execution, the compiled runtime, operating-system file I/O, and
the source-to-AST binding remain in the trusted frontend for the claim about a
particular `.vipr` file.
This limitation should not be confused with the replay soundness theorem itself.

# Independent audit procedure
%%%
tag := "audit-procedure"
%%%

An independent evaluator can use the following checklist.

## Build and smoke checks

```
lake exe cache get
lake build
lake env lean examples/vipr_checker_smoke.lean
lake env lean examples/vipr_completeness_smoke.lean
```

## End-to-end kernel replay

```
lake exe viprcheck examples/uns_knapsack.vipr \
  --proof-dir /tmp/vipr-audit
lake exe viprcheck examples/valid_min_range.vipr \
  --proof-dir /tmp/vipr-audit-min
lake exe viprcheck examples/valid_max_range.vipr \
  --proof-dir /tmp/vipr-audit-max
```

Inspect `/tmp/vipr-audit/LeanVIPRGenerated/Data.lean` and
`/tmp/vipr-audit/LeanVIPRGenerated/Proof.lean`.
The latter should contain both the concrete Boolean acceptance theorem and its
semantic consequence.

## Source hygiene

```
rg -n '\bsorry\b|\badmit\b|native_decide' LeanVIPR LeanVIPRMain.lean
rg -n '^axiom |^unsafe ' LeanVIPR LeanVIPRMain.lean
```

Expected result: no admitted proof and no use of `native_decide` in the checker
soundness path.
The `unsafe` scan should be interpreted rather than blindly counted if future
tooling code is added; the semantic theorem modules should remain free of custom
axioms and unsafe declarations.

## Axiom reports

The generated `Proof.lean` prints the axioms of
`LeanVIPR.Generated.certified`.
The expected report contains only Lean/Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`.

# Known limitations
%%%
tag := "known-limitations"
%%%

* The parser-to-source-byte binding is not formally verified.
* Full mixed-integer proof-system completeness is not formalized.
* Reconstruction is implemented only for infeasibility certificates; range
  certificates use complete replay.
* The checked-in benchmark corpus contains 20 ALU infeasibility certificates
  and 6 ALU/MIPLIB 3.0 range certificates. Exact per-certificate measurements
  for the verified array-backed checker are recorded in
  `benchmarks/results/checker.csv`.
* Kernel reduction is intentionally slower than the untrusted compiled precheck.
  Performance claims must distinguish those modes.

# Audit conclusion
%%%
tag := "audit-conclusion"
%%%

The strongest justified claim is:

> For the concrete emitted VIPR certificate AST, successful kernel checking of
> the generated acceptance theorem, followed by the proved checker-soundness
> theorem, establishes the corresponding infeasibility or result-correctness
> proposition.

The current artifact does not justify replacing “emitted certificate AST” by
“exact input bytes” without including the parser/runtime frontend in the trusted
base.
