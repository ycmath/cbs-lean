# Magic Capacity G2.5 Bridge-First Contract v0.1

**Status:** exploratory / active  
**Parent:** `research/magic-capacity-g2-local-locus-v0.1-20260829@999765c273b33ad4bdd1b00177268be63c0c85b1`  
**Branch:** `research/magic-capacity-g2p5-bridge-first-v0.1-20260829`  
**Seed:** `20260829`

## Objective order

1. Test whether the scalar insertion defect is a useful typed component of a
   system contract rather than treating it as total system cost.
2. Compare exact waiting against bounded-defect immediate insertion.
3. Test whether pairwise exactness is necessary for endpoint exactness along
   multistage paths.
4. Test the original gauge/factorization idea on exact integer block matrices.
5. Compare CBS transition boundaries against simple affine schedules and an
   ideal matched-density spacing lower bound.
6. Add only those scalar Lean lemmas that survive these bridges.

## Model A — Path-level absorption

For a width path `w=(w0,...,wm)`, define the iterated lift and direct endpoint
lift by

\[
Y_j=I_{w_{j-1}\to w_j}(Y_{j-1}),\qquad
D_j=I_{w_0\to w_j}(x).
\]

The prefix defect is `Delta_j=Y_j-D_j`. The audit records cases with some
`Delta_j>0` but `Delta_m=0`.

## Model B — Budgeted transition scheduler

At each exact periodic CBS transition phase, a policy with reserve budget `b`
may activate when `delta<=b`. The policy reports exact mean, p95, CVaR95, and
maximum waiting time over one period, plus the defect paid at activation.

The normalized cost comparison is

\[
C_b(\lambda)=\lambda\,\mathbb E[W_b]+\mathbb E[\delta_b],
\]

where `lambda` is wait cost divided by one defect-unit cost. No claim is made
that this scalar cost is a production cost model.

## Model C — Finite-batch event-grid / max-plus toy

The direct and inserted paths use the same rational grid counts. The inserted
target path is guarded by the canonical direct source-dependency threshold for
every valid output event; target events beyond the direct count are padding.

Metrics:

- valid last-event latency delta;
- maximum valid-event latency delta;
- padding-tail completion overhead;
- direct versus inserted event-work count.

This is a deterministic max-plus-style toy, not a full SDF semantics theorem.

## Model D — Integer lifting gauge toy

For intentionally factored integer maps `K=QP`, enumerate upper-unitriangular
lifting gauges `S` of depth at most two and verify exactly

\[
(QS^{-1})(SP)=QP.
\]

Metrics:

- total nonzero count;
- coefficient \(L^1\) size;
- maximum coefficient magnitude;
- condition number of `S`;
- comparison with storing the direct matrix `K`.

Two suites are required:

1. unbiased random sparse factorizations;
2. structured factorizations deliberately scrambled by lifting steps as a
   positive control.

## Model E — Boundary baselines

For each local exact set `E`, compare the CBS transition orbit with:

- the linear full-residue sweep;
- the best coprime affine sweep;
- the ideal spacing lower bound having the same period and the same number of
  admissible phases as the CBS orbit.

## Evidence boundary

The run is exploratory. It is not:

- production hardware evidence;
- a cache, DRAM, NoC, energy, or silicon benchmark;
- a full synchronous-dataflow equivalence theorem;
- a novelty or patentability determination.

## Kill and keep rules

- If `delta` does not track any system metric, retain it only as a padding-tail
  certificate.
- If reserve-1 dominates exact waiting over the relevant cost range, strict
  magic remains only for zero-reserve workloads.
- If path absorption is material, pairwise exactness cannot be an admission
  gate; use endpoint contracts.
- If gauge improvements occur only in the structured positive control, the
  gauge route becomes a compiler-recovery tool rather than a universal
  optimizer.
- If CBS increases density but worsens tail spacing, retain it as one boundary
  family and add smoothing or an affine fallback.
