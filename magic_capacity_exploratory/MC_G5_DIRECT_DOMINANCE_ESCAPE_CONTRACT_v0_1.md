# Magic Capacity G5 Direct-Dominance Escape Contract v0.1

**Status:** exploratory measured CPU gate  
**Seed:** `20260829`

## Objective

Test the factorized/gauge route against the mandatory direct operator

\[
K=QP.
\]

A conditional pass requires a nontrivial family in which exact factorized
execution improves both measured runtime and storage relative to the best tested
direct sparse or dense representation.

## Required families

1. **Densifying low-rank:** sparse `P,Q`, direct product substantially denser.
2. **Fan-out:** one shared latent state consumed by multiple `Q_j` branches.
3. **Dynamic update:** factor update versus direct incremental update and rebuild.
4. **Block-local negative control:** direct `K` intentionally sparser than the
   factors.

## Required implementations

- generated serial Numba CSR x dense;
- generated parallel Numba CSR x dense;
- SciPy CSR x dense;
- direct sparse CSR;
- direct dense BLAS with one- and five-thread stress baselines.

Generated kernels use preallocated outputs.

## Exactness gate

Every gauge arm must satisfy exact int64 endpoint semantics:

\[
(QS^{-1})(SP)X=QPX.
\]

Float32 deployment outputs are compared with direct outputs.

## Promotion conditions

- factor beats the best direct representation in every held-out densifying
  instance;
- direct storage/build costs are recorded;
- paired cache-flushed follow-up preserves the sign;
- dynamic conclusions include incremental direct updates;
- the negative control remains direct-dominated.

## Nonclaims

This gate is not GPU evidence, cross-machine replication, measured DRAM
traffic, a production compiler result, or a novelty determination.