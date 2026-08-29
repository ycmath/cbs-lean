# Magic Capacity G5 Direct-Dominance Escape Report v0.1

**Verdict:** `DIRECT_DOMINANCE_ESCAPE_PASS_CONDITIONAL`  
**Evidence class:** exploratory measured CPU kernels plus exact integer semantic checks  
**Seed:** `20260829`  
**Parent:** `research/magic-capacity-g2p5-bridge-first-v0.1-20260829@848684c433e0bbc5966280d25f66d912966706a8`

## 1. Decision

The factorized/gauge route survives the mandatory direct-operator baseline,
but only in a delimited family:

- sparse low-rank factors whose product `K=QP` densifies;
- generated sparse kernels rather than generic two-call sparse execution;
- optional shared latent fan-out;
- dynamic factors whose direct product is expensive to build or update.

A block-local negative control in which `K` itself was sparser than the factors
continued to favor direct execution. No universal factorization claim is made.

## 2. Densifying low-rank frozen grid

Configuration:

- input/output dimension: 2048;
- latent rank: 64;
- canonical factor density: 0.06;
- output branches: 1 and 4;
- batches: 1, 8, 32, 128;
- two stable hidden-basis classes;
- three held-out instances per class;
- 101 upper-unitriangular gauge candidates;
- serial and parallel generated Numba CSR kernels;
- SciPy CSR, direct CSR, and one-/five-thread dense BLAS baselines.

The direct product had median density about 18.16%. Across all 48 held-out
instance/branch/batch combinations, the best factorized implementation beat
the best tested direct representation.

| branches | batch | factor win fraction | geometric factor speedup | factor bytes | best direct bytes | direct build |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 100% | 19.85x | 128,700 | 6,102,220 | 35.7 ms |
| 1 | 8 | 100% | 14.25x | 128,700 | 6,102,220 | 36.6 ms |
| 1 | 32 | 100% | 26.16x | 128,700 | 6,102,220 | 34.7 ms |
| 1 | 128 | 100% | 24.18x | 128,700 | 6,102,220 | 38.6 ms |
| 4 | 1 | 100% | 28.89x | 333,944 | 24,409,852 | 145.5 ms |
| 4 | 8 | 100% | 37.97x | 333,944 | 24,409,852 | 160.7 ms |
| 4 | 32 | 100% | 52.28x | 333,944 | 24,409,852 | 138.1 ms |
| 4 | 128 | 100% | 46.03x | 333,944 | 24,409,852 | 144.0 ms |

Direct storage was about 47.4x the one-branch factor storage and 73.1x the
four-branch factor storage.

## 3. Generated-kernel effect

The escape was not reproduced by generic sparse calls alone. The generated
CSR x dense kernel uses preallocated output and performs work proportional to
factor nonzeros. At batch 1, SciPy could still win within the factorized family
because launch overhead dominated; from batch 8 upward, the generated kernel
was usually the factor winner.

This repositions the architecture as

`factor structure + generated kernel + typed admission`,

not as a purely algebraic gauge effect.

## 4. Cache-flushed and large-batch follow-ups

The authoritative cache-flushed follow-up used 15 alternating repeats on all
six held-out instances and compared the class factor kernel with the better of
direct parallel CSR and five-thread dense BLAS.

| class | geometric factor speedup | factor faster |
|---|---:|---:|
| stable A | 1.70x | 3/3 |
| stable B | 2.31x | 3/3 |

A noisy parallel large-batch run was superseded by a serial generated-kernel
follow-up with 15 repeats. No direct crossover appeared through batch 1024.
Minimum class speedups ranged from 10.70x to 31.96x depending on branch count
and batch.

## 5. Class gauge

Both the held-out class selector and the per-instance adaptive selector
recovered the exact hidden inverse on every test instance.

- one branch: class gauge reduced factor nnz by about 25.42% and CSR bytes by
  about 24.15%;
- four branches: nnz reduced by about 25.16% and bytes by about 23.25%;
- adaptive selection cost about 322 ms per instance in the unoptimized Python
  search;
- class selection was paid once per class and produced the same executable
  factorization.

Thus the class constant is retained as the stable-class fast path; adaptive
search remains an offline oracle/drift-recovery arm.

## 6. Dynamic updates

The direct baseline included sparse incremental outer-product updates to a
dense direct matrix, not only full rebuilds.

- factor update: about 0.005--0.033 ms;
- direct incremental update: about 0.034--11.44 ms;
- direct rebuild: about 11--68 ms.

The factorized route won all 40 tested branch/update-rank/reuse combinations,
including reuse 256. In this family dynamics strengthen an already-existing
execution win.

## 7. Negative control

A repeated block-local control was constructed with

`nnz(K) < nnz(P)+nnz(Q)`.

| batch | direct speedup over factor | factor bytes | direct bytes |
|---:|---:|---:|---:|
| 1 | 1.33x | 720,904 | 491,524 |
| 32 | 1.46x | 720,904 | 491,524 |
| 128 | 1.18x | 720,904 | 491,524 |

Direct execution won every control point. The direct baseline therefore
remains mandatory.

## 8. Active admission features

A factorized route should be considered only after evaluating:

- direct-product density;
- direct/factor storage ratio;
- latent fan-out;
- operator update rate;
- class-gauge stability;
- generated-kernel availability.

## 9. Next gate

The next prototype should combine online `P` updates, shared latent fan-out,
CBS/affine transition scheduling, fail-closed class fingerprints, and fused
generated branch kernels. Total cost must include update, direct build,
execution, storage, buffering, and waiting.

A second CPU environment is required before promotion beyond exploratory
status.

## 10. External artifact

Full package: `MagicCapacity_G5_Direct_Dominance_Escape_v0_1.zip`  
SHA-256: `a10c5680e9e9ac66b78196ff37c05cb353a35e4580c9b8fc034fdc425c1d0e1a`

The package contains the frozen config, main and follow-up scripts, raw tables,
report, contract, manifest, failure provenance, and SHA list.