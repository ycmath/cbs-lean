# cbs_lean — Lean 4 formalization for the Coffee Bean Problem (CBS)

Companion Lean 4 development for the CBS paper series:

- *The Coffee Bean Problem* (baseline paper, submitted to EJC)
- *CBS Monotonicity and Magic Numbers* (memory paper, arXiv cs.DC)
- *VW-CBS* (Eur. J. Comb.)

## Contents

| File | Scope |
|---|---|
| `CbsLean/Basic.lean` | Core definitions: cumulative shell count, level-window inversion bounds |
| `CbsLean/Rigidity.lean` | Rigidity / uniqueness results (monotone class), main-term–remainder sandwich, asymptotic equivalent |
| `CbsLean/VWNumerator.lean` | VW numerator theory |

All results compile with **zero `sorry`** and no additional axioms.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (Lean 4 v4.28.0, mathlib via `lake-manifest.json`).

```
lake build
```

Last verified full build: 2026-08-24 (8030 jobs, success; linter warnings only).

## Relation to the papers

The baseline paper's Theorem 3 proof chain (exact cumulative shell count →
level-window inversion bounds → main-term/remainder sandwich → final
asymptotic equivalent) is formalized here; the papers cite this repository
as the "companion Lean 4 development".
