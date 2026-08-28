# Magic Capacity G2.5 Bridge-First Report v0.1

**Verdict:** `BRIDGE_ACTIVE_SCALAR_DEFECT_REPOSITIONED_AS_TYPED_TAIL_METRIC`  
**Evidence class:** exploratory deterministic computation and exact integer
matrix checks  
**Seed:** `20260829`  
**Output root:** `/mnt/data/magic_capacity_g2p5_bridge_v0_1`

## 1. Executive result

The bridge-first gate changes the program in four ways.

1. Pairwise exactness is too strong: about one quarter of pointwise
   intermediate defects are absorbed before the final endpoint.
2. A one-unit reserve removes most exact-boundary waiting, and removes all
   waiting in the `h>=q` regime.
3. The scalar defect strongly tracks padding-tail overhead but does not track
   valid-output latency or total inserted work.
4. Upper-unitriangular gauges can recover hidden sparse structure, but they are
   not universal and can remain inferior to storing the direct map.

The active system object is therefore a typed contract:

\[
(\text{endpoint semantics},\ \text{padding budget},
\text{latency},\ \text{event work},\ \text{layout cost}),
\]

not a single magic/non-magic predicate.

## 2. Path-level absorption

The scan used all source residues for

- every four-width path with widths `1..16`;
- every five-width path with widths `1..10`.

| path length | paths | residue points | points with intermediate defect | absorbed at endpoint | conditional absorption |
|---:|---:|---:|---:|---:|---:|
| 4 | 65,536 | 557,056 | 200,880 | 46,507 | 23.15% |
| 5 | 100,000 | 550,000 | 306,320 | 73,405 | 23.96% |

Among paths that were globally exact at the final endpoint:

- length 4: 3,911 of 13,572
  (28.82%) were not exact at every prefix;
- length 5: 9,354 of 23,571
  (39.68%) were not exact at every prefix.

The largest absorbed intermediate defects in these frozen grids were
15 and 9.

Therefore, local pairwise exactness is a sufficient but materially
over-restrictive endpoint criterion.

## 3. Budgeted transition scheduler

Frozen grid:

- `2<=p<=24`;
- `1<=q<=24`;
- `1<=h<=48`;
- `k in {2,3,4,5,8,16}`;
- all non-global triples;
- 104,964 triple-\(k\) rows.

Exact one-period policy averages are:

| policy | mean wait | mean max wait | mean activation defect | admissible density | immediately admissible rows |
|---|---:|---:|---:|---:|---:|
| exact | 0.940340 | 3.493341 | 0.000000 | 0.682903 | 4.71% |
| reserve1 | 0.186087 | 0.720790 | 0.280221 | 0.932675 | 80.87% |
| reserve2 | 0.100229 | 0.394107 | 0.343351 | 0.963233 | 89.72% |
| immediate | 0.000000 | 0.000000 | 0.526586 | 1.000000 | 100.00% |

For every tested `h>=q` row, reserve 1 was immediately admissible. Its mean
defect payment in that regime was 0.230408. For `h<q`, reserve 1 reduced
mean waiting from 1.716329 to 0.560891.

Under the transparent normalized objective

\[
C_b(\lambda)=\lambda\mathbb E[W_b]+\mathbb E[\delta_b],
\]

the winning-policy fractions were:

| wait/defect cost ratio | exact | reserve 1 | reserve 2 | larger immediate budget |
|---:|---:|---:|---:|---:|
| 0.1 | 99.00% | 0.97% | 0.03% | 0.00% |
| 0.5 | 78.57% | 19.91% | 1.38% | 0.15% |
| 1 | 42.98% | 50.88% | 5.28% | 0.86% |
| 2 | 6.39% | 78.62% | 10.01% | 4.97% |
| 10 | 4.78% | 76.17% | 8.86% | 10.19% |

This is not a universal economic model, but it falsifies the idea that exact
waiting should be the default independent of reserve price.

## 4. Finite-batch event-grid / max-plus toy

Frozen grid:

- `1<=p,h,q<=16`;
- every `1<=x<=p`;
- middle service time in `{0.25,0.5,1,2}`;
- 139,264 rows.

Every valid target event was guarded by the direct canonical source dependency;
extra inserted target events were treated as padding.

| middle service | corr(defect, valid last latency) | corr(defect, padding-tail overhead) | corr(defect, event-work delta) |
|---:|---:|---:|---:|
| 0.25 | 0.0289 | 0.9845 | 0.0697 |
| 0.5 | 0.0011 | 0.9819 | 0.0697 |
| 1 | -0.0978 | 0.9677 | 0.0697 |
| 2 | -0.2165 | 0.8843 | 0.0697 |

At middle service time 1, even the `defect=0` group still incurred an average
of 5.871 additional events and 1.255 valid-last-event
latency.

Thus `delta` is a useful **padding-tail** coordinate, but it is not a sufficient
proxy for total work or valid-output latency.

The toy is deliberately limited. It is a max-plus-style deterministic event
model with a semantic readiness guard, not a complete SDF equivalence theorem.

## 5. Integer lifting-gauge toy

Configuration:

- rank 4;
- input and output dimension 8;
- 101 distinct upper-unitriangular lifting gauges of depth at most two;
- 64 random sparse instances;
- 64 structured instances scrambled by known lifting steps.

| suite | exact failures | identity dominated | mean nnz reduction | median nnz reduction | best factorization beats direct `K` |
|---|---:|---:|---:|---:|---:|
| random | 0 | 20.31% | 0.812 | 0.000 | 71.88% |
| structured_scrambled | 0 | 95.31% | 5.453 | 5.000 | 32.81% |

All tested gauges preserved the integer map exactly. The search recovered
hidden sparse structure in the positive-control suite, while improvements in
the random suite were much less frequent. Moreover, an exact factorization can
still be denser than storing the direct matrix.

The gauge route remains active, but as a structured compiler/layout mechanism,
not a universal compression theorem.

## 6. CBS boundary baselines

The CBS transition orbit was compared with a linear residue sweep, the best
coprime affine sweep, and an ideal matched-density spacing lower bound.

At `k=16`:

- CBS transition density exceeded the uniform local-set density in 94.34% of
  rows;
- mean density advantage was 0.222531;
- CBS maximum wait was better than the best affine cycle in 19.76% of rows,
  equal in 34.15%, and worse in 46.09%;
- relative to the ideal arrangement with the same CBS density, mean maximum-gap
  excess was 2.493655 phases.

Therefore CBS can concentrate visits inside the admissible set, but the same
nonuniformity can cluster misses and worsen tail waiting. CBS is retained as
one boundary family, not the default capacity grammar.

## 7. Research disposition

### Keep

- source/transition distinction;
- scalar defect as a padding-tail budget;
- exact periodic transition scheduler;
- path-level endpoint contracts;
- upper-unitriangular lifting gauges for structured factorizations.

### Demote

- pairwise exactness as an admission gate;
- bi-magic as the default operation contract;
- `delta=0` as a total-cost certificate;
- CBS as a universal boundary family.

### Next gate

Build one typed compositional prototype with:

1. a small multirate dataflow graph;
2. an exact or masked endpoint linear operator;
3. a max-plus latency state;
4. a reserve budget on padding events;
5. a selectable CBS or affine transition scheduler;
6. an upper-unitriangular gauge choice.

The acceptance test is joint:

\[
\text{endpoint semantics exact}
\land
\text{buffer/latency contract met}
\land
\text{movement cost improved}.
\]

If no joint improvement appears, the arithmetic line should be reduced to a
specialized reblocking/padding analysis tool.

## 8. Literature boundary

The bridge uses established neighboring models rather than claiming them as
new:

- Lee and Messerschmitt, static scheduling of synchronous dataflow, 1987;
- max-plus matrix semantics for SDF timing, throughput, and latency;
- Sweldens' lifting scheme and in-place biorthogonal transforms.

No novelty claim is made for these models or for their standard properties.
