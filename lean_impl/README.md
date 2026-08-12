# AptpCheck

A from-scratch **Lean 4** reimplementation of [`aptpchecker`](../README.md): a
formally-verified checker for **Activation-Pattern-Tree Proofs (APTP)** of
neural-network properties.

- **Exact.** All arithmetic is over `ℚ`; network weights are decoded bit-exactly
  from IEEE-754 (no `Float`, no rounding).
- **No trusted solver.** SCIP runs as an *untrusted* oracle; its **VIPR**
  certificate is re-checked in Lean over exact rationals. (Gurobi is dropped
  because it cannot export a proof.)
- **Kernel-checked.** Soundness is proved against Mathlib and checked by the Lean
  kernel — no `native_decide` on the trusted path.
- **No Python.** The tool reads an exact `.net` network format and the existing
  `.aptp` proof format; nothing calls Python.

See [DESIGN.md](DESIGN.md) for the full architecture, the soundness decomposition
(per-leaf refutation + coverage + encoding soundness), the data contract, the
trusted computing base, and the roadmap. A CAV paper draft is in [paper/](paper/).

## Build

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager). The toolchain and Mathlib revision are pinned by `lean-toolchain` and
`lakefile.toml`.

```bash
# one-time: fetch Mathlib and its prebuilt cache
lake exe cache get
# build the library + `aptpcheck` executable
lake build
# run
lake exe aptpcheck
```

## Status

Implemented and kernel-checked:

| Module | Contents |
|---|---|
| `AptpCheck/Numeric/Float.lean` | exact `float32/float64 → ℚ` decoders |
| `AptpCheck/Ast/Sexpr.lean` | statement lexer + S-expr parser + exact decimal→ℚ |
| `AptpCheck/Ast/Net.lean` + `Model/Network.lean` | `.net` parser + exact network eval (validated vs. Python) |
| `AptpCheck/Ast/Aptp.lean` | `.aptp` → `Problem` (validated vs. `read_aptp.py`) |
| `AptpCheck/Cert/LinComb.lean`  | Farkas checking-direction lemma + reflective `CheckLin` |
| `AptpCheck/Coverage/Tautology.lean` | DNF coverage check + `coverage_sound` |

Planned (see DESIGN.md §7–8): the network MILP encoding (with the
encoding-soundness theorem), the VIPR parser + `lin`/`rnd`/`uns` replay, and the
composed top-level `certified_sound` theorem.
