# Magic Capacity G1 Prior-Art and Repositioning Note v0.1

**Status:** `REPOSITIONED_PRIOR_ART_FOUND`  
**Date:** 2026-08-28  
**Evidence class:** targeted primary-source literature audit plus algebraic translation  
**Frozen parent:** G0 head `b066671d9f4fd984b5e8b116b9a60e9d479c104f`  
**Exploratory branch:** `research/magic-capacity-g1-characterization-v0.1-20260828`

## 1. Result of the audit

The global exact-insertion classification developed in G0/G1 is not treated as
a new theorem claim.

Jeffrey C. Lagarias and D. Harry Richman classify positive dilation pairs whose
dilated floor functions have nonnegative commutator in:

> J. C. Lagarias and D. H. Richman, *Dilated floor functions having
> nonnegative commutator I. Positive and mixed sign dilations*, Acta
> Arithmetica 187 (2019), no. 3, 271–299,
> arXiv:1806.00579, DOI:10.4064/aa180602-21-9.

Their Theorem 1.2 states that for positive `alpha,beta`, the nonnegative
commutator condition holds exactly when

\[
  m\alpha\beta+n\alpha=\beta
\]

for some nonnegative integers `m,n`, not both zero.  The paper explicitly
relates this positive-dilation classification to Beatty sequences and the
2-generator Frobenius problem.

## 2. Translation to the magic-capacity kernel

The G0 index lift is

\[
I_{p\to q}(x)=\left\lceil\frac{qx}{p}\right\rceil.
\]

For positive endpoint widths `p,q` and inserted width `h`, global exactness is

\[
I_{h\to q}(I_{p\to h}(x))=I_{p\to q}(x)
\quad\text{for every integer index }x.
\]

The direct lift is always no larger than the inserted composite.  Exactness is
therefore equivalent to

\[
q\left\lceil\frac{hx}{p}\right\rceil
\le
h\left\lceil\frac{qx}{p}\right\rceil
\quad\text{for every }x.
\]

Under the substitution

\[
\alpha=\frac{p}{h},\qquad \beta=\frac{p}{q},
\]

this is the positive rounding/commutator relation classified by
Lagarias–Richman.  Their Diophantine condition becomes

\[
m\frac{p}{h}\frac{p}{q}+n\frac{p}{h}=\frac{p}{q},
\]

and multiplication by `hq/p` yields

\[
 h=mp+nq.
\]

Thus the two-generator semigroup condition

\[
h\in\langle p,q\rangle
=\{mp+nq:m,n\in\mathbb N\}
\]

is a rational-width specialization/re-expression of an existing
classification theorem.

## 3. Claim lock

The following claims are prohibited without a substantially different object
or theorem:

- that the equivalence `global exact insertion iff h in <p,q>` is novel;
- that the associated two-generator condition was first discovered in this
  program;
- that the finite grids establish novelty or priority;
- that the arithmetic theorem alone establishes a hardware result.

The new Lean files are retained as an independently derived formal
specialization and as infrastructure for the CBS-linked research line.  No
claim is made here that this is the first formalization of the
Lagarias–Richman result; that question requires a separate formal-library
search.

## 4. Research line retained after repositioning

The audit does **not** collapse the magic-capacity program.  It moves the
research target from the already-classified global relation to the following
objects:

1. **CBS source reconciliation.**  The published-memory-paper binomial used as
   a magic number is a next-shell increment rather than the cumulative count.
2. **Local exact-residue sets.**  Even when global exactness fails, a nontrivial
   subset of source residues has zero insertion defect.
3. **CBS magic loci.**  Intersect the local exact-residue set with the CBS
   cumulative and next-shell sequences modulo the source width.
4. **State/transition/bi-magic density and gap laws.**  Prove periodicity,
   density, and maximal waiting-gap results rather than merely enumerate them.
5. **Filtered-matrix and runtime translation.**  Determine when residue-level
   exactness preserves an existing block system and reduces actual movement,
   latency, or reconfiguration cost.
6. **Near-magic perturbation.**  Bound numerical, queueing, and memory costs
   when the arithmetic defect is small but nonzero.

## 5. Current epistemic status

- Lagarias–Richman prior-art mapping: strong, source-backed algebraic match.
- G1 Lean characterization: theorem-checking evidence for the specialization.
- Finite grids: exploratory exact-integer computation only.
- Local CBS magic-locus theory: active theorem-generation target.
- Hardware or industrial advantage: untested.
