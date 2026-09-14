# Compiled replay measurements

`checker.csv` contains one warmed, sequential native-CLI measurement for every
checked-in benchmark certificate using the verified array-backed checker.

Environment:

- Apple M3 Pro, 12 cores, 36 GB
- macOS 26.6.2
- Lean 4.31.0
- SCIP 10.0.3 for certificate generation

Times are seconds from `/usr/bin/time -p`. All 46 measured runs pass:

- 20 infeasibility certificates in complete replay;
- the same 20 certificates after dependency slicing;
- 6 objective-range certificates in complete replay.

Aggregate infeasibility result:

| Certificates | Full steps | Sliced steps | Full time | Sliced time |
|---:|---:|---:|---:|---:|
| 20 | 124,382 | 33,568 | 8.49 s | 3.44 s |

The compiled path is an explicitly untrusted performance reference. It does not
replace kernel checking of a concrete run.

## Verified array-backed checker

The implementation in `LeanVIPR/Cert/ViprChecker.lean` uses an
array-backed pool, fuses validation with replay, avoids the second final-result
replay, and computes each linear combination once.

| Certificate modes | Runs | Wall time |
|---|---:|---:|
| Infeasibility, full | 20 | 8.49 s |
| Infeasibility, sliced | 20 | 3.44 s |
| Range, full | 6 | 28.41 s |
| **Overall** | **46** | **40.34 s** |

All 46 timed invocations pass. The formal theorems
`checkVipr_refines` and `checkVipr_sound` connect this implementation
directly to the declarative proof system and full-result semantics. Native
timings still include the Lean compiler and runtime.

## Official C++ pipeline

`cpp.csv` measures the official single-threaded completion-and-checking path:

```text
viprcomp --soplex=off --threads=1 certificate.vipr
viprchk certificate_complete.vipr
```

Every raw certificate contains `lin weak`, so direct `viprchk` execution is not
the applicable reference workflow. The pipeline accepts 13 of 26 completed
files. In the other 13 cases `viprcomp` exits successfully, but `viprchk`
rejects the emitted certificate. Consequently, failed rows contain time to
rejection and must not be interpreted as successful-checking performance.
