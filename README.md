# cbs_lean — Lean 4 formalization for the Coffee Bean Problem (CBS)

Companion Lean 4 development for the CBS paper series:

- *The Coffee Bean Problem* (baseline paper, preprint:
  [doi:10.5281/zenodo.22071069](https://doi.org/10.5281/zenodo.22071069))
- *CBS Monotonicity and Magic Numbers* (memory paper:
  [doi:10.5281/zenodo.22071007](https://doi.org/10.5281/zenodo.22071007))
- *VW-CBS* (preprint:
  [doi:10.5281/zenodo.22074703](https://doi.org/10.5281/zenodo.22074703))
- *Coffee-Bean Maximality for Width-Normalized Label Systems* (preprint:
  [doi:10.5281/zenodo.22740806](https://doi.org/10.5281/zenodo.22740806))
- *A Macaulay-Type Lower Bound for Nested Multichains and Lecture Hall Polytopes*
  (preprint: [doi:10.5281/zenodo.23373846](https://doi.org/10.5281/zenodo.23373846))

The software version series is archived at
[doi:10.5281/zenodo.22070763](https://doi.org/10.5281/zenodo.22070763).
Archived releases: [v1.0.0](https://doi.org/10.5281/zenodo.22070764) (baseline
and VW numerator modules), [v1.1.0](https://doi.org/10.5281/zenodo.22741194)
(2026-09-14, adds the six `Cb*` maximality modules) and v1.2.0 (adds the Macaulay
modules `MacaulayOps`, `PathCount`, `NestedChains`, `NestedChainsStrict`,
`NestedChainsComplement`, `NestedChainsWords`, `LectureHallMacaulay`, `CbMacaulay`).
Cite the concept DOI above, or the version DOI of the release you used.
The memory and VW links above are concept DOIs for their version series;
the inspected paper versions are respectively
[22075228](https://doi.org/10.5281/zenodo.22075228) and
[22074704](https://doi.org/10.5281/zenodo.22074704).

## Contents

| File | Scope |
|---|---|
| `CbsLean/Basic.lean` | Template stub only (`def hello := "world"`); no CBS content |
| `CbsLean/Rigidity.lean` | Baseline counting and asymptotic results: shell counts and cumulative counts (`coffeeBeanShell`, `coffeeBeanCumulative`, `coffeeBeanCumulative_closedForm`), level-window inversion bounds (`coffeeBeanLevelWindow_realRootBounds`), equal-cost / weighted-gap rigidity in the monotone class, main-term–remainder sandwich (`coffeeBeanMinCost_normalized_squeeze`), and the final asymptotic equivalent (`coffeeBeanMinCost_isEquivalent`) |
| `CbsLean/VWNumerator.lean` | VW-CBS numerator theory: mixed-radix digit box (`digitBox`), the division-free ceiling recurrence (`ceilScaled`, `mixedRadixStep`, `mixedRadixAux`), and weighted digit sums — supports the VW-CBS paper, not the baseline paper |
| `CbsLean/CbMaximality.lean` | cb maximality theorem (W1): room multisets of a width vector as a branching process (`rooms`, `Phi`, `chainMap`), effective width `kappa`, the predicates `Wpred`/`Lam`/`Ppred`, Lemmas A–D, **Theorem 5** `ppred_rooms` and **Theorem 6** `cb_maximality` (cumulative dominance: for nondecreasing widths with `k₁ = 1`, `N_K(L) ≤ N_cb(k)(L)` implies `N_K(l) ≤ N_cb(k)(l)` for all `l ≤ L`) |
| `CbsLean/CbLabels.lean` | Identification of the room multisets with the actual VW label set: `vwRev K` = `digitBox K` filtered by width-normalized monotonicity, `card_heads` (`⌊(k-c)k'/k⌋` rooms), `roomMS_cons` (branching recursion on labels), `shell_eq_card` (`shell w l` is the number of VW labels of length `l + 2`) |
| `CbsLean/CbCost.lean` | Breadth-first cost: layer-cake `bfCost`, its monotonicity under cumulative dominance, the level/remainder formula of the baseline paper's Theorem 2, `coffeeBeanMinCost_eq_bfCost` (agrees with `Rigidity.lean`), `bfCost_eq_sum_lengths`, and the cost form of Theorem 6 `minCost_cb_le` |
| `CbsLean/CbStrict.lean` | Strictness of cb maximality: strict forms of Claim K and Claim S (`claimK_strict`, `claimS_strict`) and `cb_maximality_strict` — under the hypothesis of `cb_maximality`, if the second width is smaller than `k` the cumulative inequality is strict at every intermediate level |
| `CbsLean/CbTailInduction.lean` | Lemma C by tail induction: `ppred_succ_of_ppred` (`Ppred l Y → Ppred (l+1) (Phi c Y)`) proved directly by induction on the target shift with two cases (within/over the cb budget), using only `N_Phi`, Pascal, the hockey stick and the reduction `E (Phi id Y) (J c v) ≤ E (Phi c Y) v`; `ppred_rooms_all` re-derives Theorem 5 at every level without Lemmas A, C, D |
| `CbsLean/CbRigidity.lean` | Rigidity of cb maximality: `k ≤ k₂` gives `cumShellCb k L ≤ cumShell w L` for all `L` (`rigidity_le`), with equality iff `K = cb(k)` below `L` (`rigidity_eq_iff`); the constant system has the cb shells (`shell_const`); hence `cb_maximality_strict_of_ne` — strictness at intermediate levels for every `K ≠ cb(k)` |
| `CbsLean/MacaulayOps.lean` | Macaulay representations by greedy top coefficient (`top`) and the operators `up D x = x^⟨D⟩`, `low D x = x_⟨D⟩`, `S D x = x - x_⟨D⟩`, `kk D x = x^{(D)}`; Lemma 2.1 of the Macaulay paper: splitting identities (`up_split`, `low_split`, `S_split`, `S_iterate_split`), monotonicity (`low_mono`, `S_mono`, `up_strictMono`), `low_up` (`(y^⟨D⟩)_⟨D+1⟩ = y`), `up_eq_add_up_S` and `up_eq_sum_iterate` (`x^⟨D⟩ = ∑_r S_D^r(x)`), `up_choose`, `kk_add_self` |
| `CbsLean/PathCount.lean` | Paths through a sequence of finite sets with step relations, counted by their endpoint (`pathEnds`); `card_paths`: the recursion counts the tuple set `paths` |
| `CbsLean/NestedChains.lean` | **Theorem 3.1** of the Macaulay paper: for nested finite sets `A 0 ⊆ A 1 ⊆ ⋯` in a linear order, the multichain counts satisfy `up D (h A D) ≤ h A (D + 1)` (`nested_reverse_macaulay`), with equality for constant sequences (`h_const`, `nested_reverse_macaulay_const`); the room bound `room_bound`, `room_bound_tail` (Corollary 3.3); `h_eq_card` (`h` counts monotone tuples) |
| `CbsLean/NestedChainsStrict.lean` | **Theorem 3.4**: the Kruskal–Katona analogue for strict chains, `kk D (hS A D) ≤ hS A (D + 1)` (`nested_reverse_kk`), equality `hS = C(n, D)` for constant sequences (`hS_const`, `nested_reverse_kk_const`), `hS_eq_card` |
| `CbsLean/NestedChainsComplement.lean` | **Theorem 4.3** (complement form) for multichains and strict chains: the bound `Phi D x = Φ_D(x)` (`ctop`, `Phi`, `Phi_band`), the Galois correspondence `galois` (Lemma 2.2), Lemma 4.2 (`Phi_strictMono`, `Lmax_eq`, `Phi_fixed`, `up_le_Phi`), and `nested_complement` (`Φ_D(h A D) ≤ h A (D + 1)`), `nested_complement_strict` (`Φ_D(x) - x ≤ hS A (D + 1)`) |
| `CbsLean/NestedChainsWords.lean` | **Theorem 4.3 for every word** of strict and weak relations: `ε`-chain counts `hW` (`hW_eq_card`, `hW_false`, `hW_true`), identity (2) `hW_weak_eq`, and `complement_word_le`, `complement_word_lt`, with the corresponding extensions of Theorems 3.1 and 3.4 (`macaulay_word_le`, `kk_word_lt`) |
| `CbsLean/LectureHallMacaulay.lean` | **Corollary 6.1** (Macaulay inequalities): lattice-point counts of `s`-lecture hall polytopes (`lhClosed`, `lhHalfOpen`, identified with the lattice-point sets by `lhClosed_eq_card`, `lhHalfOpen_eq_card`) satisfy `up D (h_s(D)) ≤ h_s(D + 1)` for positive nondecreasing `s`, closed and half-open (`lh_reverse_macaulay`, `lh_reverse_macaulay_halfOpen`, and the finite-prefix forms `…_of_prefix`); ceiling maps `ceilStep`, lifts `lift`, nested sets `lhSets`, count identity `ends_lhSets` |
| `CbsLean/CbMacaulay.lean` | **Corollary 7.2**: the room multisets are the rooms of half-open lecture hall points (`rooms_succ_eq_map`, `count_lastMS`), so `shell w l = h°_w(l + 1)` (`shell_eq_lhHalfOpen`) and `1 + cumShell w d = h_w(d)` (`one_add_cumShell`); reverse Macaulay growth of shells and cumulative counts (`shell_reverse_macaulay`, `cumulative_reverse_macaulay`), single crossing against maximal Macaulay growth (`single_crossing`), and a second proof of cb maximality, `cb_maximality_macaulay`, with the same statement as `cb_maximality` and no effective width |

All results compile with **zero `sorry`** and no additional axioms.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain` (Lean 4 v4.28.0, mathlib via `lake-manifest.json`).

```
lake build
```

Last verified full build: 2026-10-14 (8042 jobs, success; the only warnings are two
pre-existing linter warnings in `Rigidity.lean`).

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

Scope note: `Rigidity.lean` contains the Theorem 4 chain described above.
The later `CbCost.lean` additionally proves the finite-n breadth-first
level/remainder formula (`bfCost_eq_level_formula`), its equality with the
sum of the n shortest lengths (`bfCost_eq_sum_lengths`), and the connection
to `coffeeBeanMinCost`. This does not assert a formalization of every
statement of Theorem 2: the classification and counting of all optimal
label subsets are not supplied by those cost identities.

## Continuous integration

`Lean Action CI / build` checks the pinned Lean project on pushes, pull
requests, and manual runs. A separate `documentation` job generates API
docs on pushes to `master` and retains them as a downloadable Actions
artifact. Neither job deploys a website; GitHub Pages is not required.
Documentation generation uses a fixed docgen-action revision supporting
`deploy: false`. A future Pages deployment should be configured separately
and restricted to the default branch.

## cb maximality (W1 note, 2026-09-04)

`CbMaximality.lean`, `CbLabels.lean`, `CbCost.lean`, `CbStrict.lean`, `CbRigidity.lean` and
`CbTailInduction.lean` formalize the
theorem of the W1 proof note
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
| Strict Claim K / Claim S, strictness at intermediate levels | `claimK_strict`, `claimS_strict`, `cb_maximality_strict` |
| Rigidity (`k ≤ k₂ ⇒ N_cb(L) ≤ N_K(L)`, equality iff `K = cb(k)`) | `rigidity_le`, `rigidity_lt`, `rigidity_eq_iff` |
| Strictness for every `K ≠ cb(k)` | `cb_maximality_strict_of_ne` |
| Theorem 5 by tail induction (second proof, no Lemmas A/C/D) | `ppred_succ_of_ppred`, `ppred_rooms_all` |

All six files build with zero `sorry`; `#print axioms` on `cb_maximality`, `shell_eq_card`,
`minCost_cb_le`, `cb_maximality_strict`, `rigidity_eq_iff`, `cb_maximality_strict_of_ne` and
`ppred_rooms_all` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Macaulay-type lower bound (2026-10)

`MacaulayOps.lean`, `PathCount.lean`, `NestedChains.lean`, `NestedChainsStrict.lean`,
`NestedChainsComplement.lean`, `NestedChainsWords.lean`, `LectureHallMacaulay.lean` and
`CbMacaulay.lean` formalize the companion paper *A Macaulay-Type
Lower Bound for Nested Multichains and Lecture Hall Polytopes*: for nested finite sets
`A_1 ⊆ A_2 ⊆ ⋯` of a totally ordered set, the number `h(D)` of multichains `q_1 ≤ ⋯ ≤ q_D` with
`q_i ∈ A_i` satisfies `h(D+1) ≥ h(D)^⟨D⟩`, the reverse of Macaulay's bound for Hilbert functions.
Levels are indexed from `0` in Lean (`A 0` is the paper's `A_1`, `s 0` is `s_1`).

| Paper statement | Lean theorem |
|---|---|
| Lemma 2.1 (a), one term at a time | `S_split`, `S_iterate_split` |
| Lemma 2.1 (b) | `low_succ_le`, `low_le_succ`, `low_mono`, `S_mono` |
| Lemma 2.1 (c) | `low_up` |
| Lemma 2.1 (d) | `up_eq_add_up_S`, `up_eq_sum_iterate` |
| Lemma 2.1 (e) | `up_strictMono` |
| Lemma 2.2 (Galois correspondence) | `galois`, `le_up_low` |
| Lemma 2.3 (band lemma) | `S_lt_band` |
| `h_A(D)` counts multichains | `h_eq_card` |
| Theorem 3.1 (inequality) | `nested_reverse_macaulay` |
| Theorem 3.1 (equality for constant sequences) | `h_const`, `nested_reverse_macaulay_const` |
| Corollary 3.3 (room bound) | `room_bound` (`r < m`), `room_bound_tail` (`r ≥ m`) |
| Theorem 3.4 (strict chains, Kruskal–Katona operator) | `nested_reverse_kk`, `hS_const`, `nested_reverse_kk_const` |
| Definition 4.1 (`Φ_D`) | `ctop`, `Phi`, `Phi_band`, `Phi_choose` |
| Lemma 4.2 (a), (b), (c) inequality | `Phi_strictMono`, `Lmax_eq`, `Phi_fixed`, `up_le_Phi` |
| Theorem 4.3, words `(≤, …, ≤)` and `(<, …, <)` (Corollary 4.4) | `nested_complement`, `nested_complement_strict` |
| `h^ε_A(D)` counts `ε`-chains; identity (2) | `hW_eq_card`, `hW_weak_eq` |
| Theorem 4.3, every word | `complement_word_le`, `complement_word_lt` |
| Theorems 3.1 and 3.4 for every word | `macaulay_word_le`, `kk_word_lt` |
| Corollary 6.1, the Macaulay inequalities for `h_s` and `h°_s` | `lh_reverse_macaulay`, `lh_reverse_macaulay_halfOpen`, `lh_reverse_macaulay_of_prefix`, `lh_reverse_macaulay_halfOpen_of_prefix` |
| `h_s(D)`, `h°_s(D)` count lattice points | `lhClosed_eq_card`, `lhHalfOpen_eq_card` |
| Lemma 7.1 (`k₁ = 1`) | `one_add_cumShell`, `shell_eq_lhHalfOpen` |
| Corollary 7.2 (1) | `cumulative_reverse_macaulay` |
| Corollary 7.2 (2) (single crossing) | `single_crossing` |
| Corollary 7.2 (3) (cb maximality, second proof) | `cb_maximality_macaulay` |

Not formalized: the equality cases of Lemma 4.2(c) and
Corollary 4.7, Lemma 2.4 and the results that use it (Corollaries 4.6 and 7.4), Proposition 4.8,
and the word and complement forms of Corollary 6.1. Lemma 2.1(a) is formalized one Macaulay
term at a time.

`cb_maximality_macaulay` has the same statement as `cb_maximality`; its proof uses neither the
effective width `kappa` nor the predicates `Wpred`/`Lam`/`Ppred`. All eight files build with zero
`sorry`; `#print axioms` on the theorems above reports only `propext`, `Classical.choice`,
`Quot.sound`. Paper numbers refer to the version of 2026-10-14 (18 pages).
