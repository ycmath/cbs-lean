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
| `CbsLean/CbMaximality.lean` | cb maximality theorem (W1): room multisets of a width vector as a branching process (`rooms`, `Phi`, `chainMap`), effective width `kappa`, the predicates `Wpred`/`Lam`/`Ppred`, Lemmas A–D, **Theorem 5** `ppred_rooms` and **Theorem 6** `cb_maximality` (cumulative dominance: for nondecreasing widths with `k₁ = 1`, `N_K(L) ≤ N_cb(k)(L)` implies `N_K(l) ≤ N_cb(k)(l)` for all `l ≤ L`) |
| `CbsLean/CbLabels.lean` | Identification of the room multisets with the actual VW label set: `vwRev K` = `digitBox K` filtered by width-normalized monotonicity, `card_heads` (`⌊(k-c)k'/k⌋` rooms), `roomMS_cons` (branching recursion on labels), `shell_eq_card` (`shell w l` is the number of VW labels of length `l + 2`) |
| `CbsLean/CbCost.lean` | Breadth-first cost: layer-cake `bfCost`, its monotonicity under cumulative dominance, the level/remainder formula of the baseline paper's Theorem 2, `coffeeBeanMinCost_eq_bfCost` (agrees with `Rigidity.lean`), `bfCost_eq_sum_lengths`, and the cost form of Theorem 6 `minCost_cb_le` |

All results compile with **zero `sorry`** and no additional axioms.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (Lean 4 v4.28.0, mathlib via `lake-manifest.json`).

```
lake build
```

Last verified full build: 2026-09-04 (8033 jobs, success; linter warnings only).

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

## cb maximality (W1 note, 2026-09-04)

`CbMaximality.lean`, `CbLabels.lean` and `CbCost.lean` formalize the theorem of the W1 proof note
(`W1_Proof_Note_v0_1.md`, companion to the VW-CBS paper): among width-normalized label systems with
nondecreasing widths and a single root (`k₁ = 1`), the coffee-bean system `cb(k) = VW(1, k, …, k)`
has the largest cumulative shell counts, hence the smallest breadth-first cost, at every level up to
any level where its cumulative count dominates.

| Note statement | Lean theorem |
|---|---|
| Lemma A (`𝒫_l ⇒ Λ_l`) | `lam_of_ppred` |
| Lemma B (branching bookkeeping) | `N_Phi`, `roomMS_cons` |
| Lemma C (`Λ_l ⇒ 𝒫_{l+1}`) | `ppred_succ_of_lam` |
| Lemma D (distinct base, paper level 3) | `ppred_one_of_distinct` |
| Theorem 5 (Claim W at every level) | `ppred_rooms` |
| Proposition 4 (summation form), Claim K, Claim S | `shellCb_succ_kappa_le_phi_id`, `claimK`, `claimS` |
| Theorem 6 (cumulative dominance) | `cb_maximality` |
| `shell w l` = number of VW labels of length `l + 2` | `shell_eq_card` |
| Theorem 6, cost form | `minCost_cb_le` |

All three files build with zero `sorry`; `#print axioms` on `cb_maximality`, `shell_eq_card` and
`minCost_cb_le` reports only `propext`, `Classical.choice`, `Quot.sound`.
