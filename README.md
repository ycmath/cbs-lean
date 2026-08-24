# cbs_lean — Lean 4 formalization for the Coffee Bean Problem (CBS)

Companion Lean 4 development for the CBS paper series:

- *The Coffee Bean Problem* (baseline paper, preprint:
  [doi:10.5281/zenodo.22071069](https://doi.org/10.5281/zenodo.22071069))
- *CBS Monotonicity and Magic Numbers* (memory paper:
  [doi:10.5281/zenodo.22071007](https://doi.org/10.5281/zenodo.22071007))
- *VW-CBS* (preprint:
  [doi:10.5281/zenodo.22074703](https://doi.org/10.5281/zenodo.22074703))

This repository is archived at
[doi:10.5281/zenodo.22070763](https://doi.org/10.5281/zenodo.22070763).

## Contents

| File | Scope |
|---|---|
| `CbsLean/Basic.lean` | Template stub only (`def hello := "world"`); no CBS content |
| `CbsLean/Rigidity.lean` | All CBS baseline-paper content: shell counts and cumulative counts (`coffeeBeanShell`, `coffeeBeanCumulative`, `coffeeBeanCumulative_closedForm`), level-window inversion bounds (`coffeeBeanLevelWindow_realRootBounds`), equal-cost / weighted-gap rigidity in the monotone class, main-term–remainder sandwich (`coffeeBeanMinCost_normalized_squeeze`), and the final asymptotic equivalent (`coffeeBeanMinCost_isEquivalent`) |
| `CbsLean/VWNumerator.lean` | VW-CBS numerator theory: mixed-radix digit box (`digitBox`), the division-free ceiling recurrence (`ceilScaled`, `mixedRadixStep`, `mixedRadixAux`), and weighted digit sums — supports the VW-CBS paper, not the baseline paper |

All results compile with **zero `sorry`** and no additional axioms.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (Lean 4 v4.28.0, mathlib via `lake-manifest.json`).

```
lake build
```

Last verified full build: 2026-08-24 (8030 jobs, success; linter warnings only).

## Relation to the papers

The baseline paper's **Theorem 4** proof chain (exact cumulative shell count →
level-window inversion bounds → main-term/remainder sandwich → final
asymptotic equivalent) is formalized here, as the four theorems

| Paper step | Lean theorem |
|---|---|
| exact cumulative shell count | `coffeeBeanCumulative_closedForm` |
| level-window inversion bounds | `coffeeBeanLevelWindow_realRootBounds` |
| main-term/remainder sandwich | `coffeeBeanMinCost_normalized_squeeze` |
| final asymptotic equivalent (Theorem 4) | `coffeeBeanMinCost_isEquivalent` |

all in `CbsLean/Rigidity.lean`. The papers cite this repository as the
"companion Lean 4 development".

Scope note: the formalization covers the asymptotic analysis of the
closed-form cost (the Theorem 4 chain). It does **not** formalize the
finite-n optimality claim of Theorem 2.
