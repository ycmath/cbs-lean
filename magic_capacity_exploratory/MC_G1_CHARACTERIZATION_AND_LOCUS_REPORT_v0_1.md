# Magic Capacity G1 Characterization and Locus Report v0.1

**Verdict:** `G1_GLOBAL_CLASSIFICATION_FORMALIZED_LOCAL_LOCUS_ACTIVE`  
**Evidence split:** theorem-backed arithmetic / exploratory exact-integer grid  
**Date:** 2026-08-28

## 1. Provenance

| Field | Value |
|---|---|
| repository | `ycmath/cbs-lean` |
| frozen G0 parent | `b066671d9f4fd984b5e8b116b9a60e9d479c104f` |
| G1 branch | `research/magic-capacity-g1-characterization-v0.1-20260828` |
| G1 source head before this report | `1f1d56ad39806accdc65741d67dc7412e6ccd4b8` |
| Lean toolchain | repository-pinned Lean 4 v4.28.0 / mathlib |
| randomness | none |
| seed | `null` |
| local grid config SHA-256 | `4b434b981dcfe31b50f0c6261159f5b9ebc682e0072f6d19d3af2edd4cb5da8c` |

No published paper, G0 report, `Rigidity.lean`, `VWNumerator.lean`, G0 branch,
or `master` was overwritten.

## 2. Formal characterization

Let

\[
I_{p\to q}(x)=\left\lceil\frac{qx}{p}\right\rceil,
\qquad
C_{p,h,q}(x)=I_{h\to q}(I_{p\to h}(x)).
\]

Define global exact insertion by

\[
C_{p,h,q}(x)=I_{p\to q}(x)\quad\text{for all }x\in\mathbb N.
\]

### 2.1 Coprime endpoints

`CbsLean/MagicCapacityCharacterization.lean` proves, for positive coprime
`p,q` and positive `h`,

\[
\forall x,\ C_{p,h,q}(x)=I_{p\to q}(x)
\quad\Longleftrightarrow\quad
h\in\langle p,q\rangle.
\]

The necessity proof uses two modular witnesses:

- a residue `x` satisfying `qx = -1 mod p`;
- the Apéry representative `j` satisfying `qj = h mod p`.

Exactness forces `qj <= h`; congruence then gives `h=qj+ap`.

### 2.2 Arbitrary positive endpoints

`CbsLean/MagicCapacityCharacterizationGeneral.lean` removes the coprimality
restriction:

1. exactness at `x=p/gcd(p,q)` forces `gcd(p,q) | h`;
2. common positive scaling cancels from the index-lift equations;
3. division by the endpoint gcd reduces to the coprime theorem;
4. the normalized semigroup certificate scales back.

The resulting theorem is

\[
\boxed{
\forall x,\ C_{p,h,q}(x)=I_{p\to q}(x)
\iff
h\in\langle p,q\rangle
}
\]

for positive `p,h,q`.

This classification is retained as a Lean specialization and research kernel,
not as a novelty claim; see `MC_G1_PRIOR_ART_AND_REPOSITIONING_v0_1.md`.

## 3. Frozen exploratory grids

The executable notebook uses exact integer arithmetic and two distinct scans.

### 3.1 Independent all-residue calibration

| parameter | value |
|---|---:|
| `p` | 1 through 64 |
| `q` | 1 through 64 |
| `h` | 1 through 512 |
| triples | 2,097,152 |
| tested residues per triple | all `x=0,...,p-1` |
| classification mismatches | **0** |
| largest observed insertion defect | 63 |

This scan independently evaluates the definition of global exactness rather
than relying on the proof witness.

### 3.2 Critical-witness scan

| parameter | value |
|---|---:|
| `p` | 1 through 128 |
| `q` | 1 through 128 |
| `h` | 1 through 4096 |
| triples | 67,108,864 |
| classification/witness mismatches | **0** |
| largest observed witness defect | 127 |

This larger scan uses the theorem-motivated obstruction witness.  It is not
substituted for the independent all-residue scan.

### 3.3 Artifact identifiers

| artifact | SHA-256 |
|---|---|
| Colab notebook | `0427366d5d92ea4db845c8b904a76d64608bedf5b3ae3e8326950476931d2ff3` |
| Colab package | `c79b5fc37dd80360b154d5fa021f21b620281de85f7d92581521598d5b004631` |
| local STANDARD result ZIP | `432f7ce8b4ed110146573d5418976cc5a974d22b7cf43e02af52a94868988eac` |

The grid verdict is

`EXPLORATORY_NO_COUNTEREXAMPLE_IN_FROZEN_GRIDS`.

It is not system-level confirmatory evidence.

## 4. Local exact-residue sets

For a fixed triple define

\[
E_{p,h,q}
=\{r\in\mathbb Z/p\mathbb Z:\delta_{p,h,q}(r)=0\}.
\]

Global exactness means `E` is the whole residue ring.  The important new
observation is that non-global triples often have large nontrivial `E`.

Examples from one complete source period:

| `(p,h,q)` | status | defect polynomial over residues |
|---|---|---|
| `(4,6,8)` | not globally exact | `2 + 2 z` |
| `(5,7,8)` | not globally exact | `3 + 2 z` |
| `(8,12,16)` | not globally exact | `4 + 4 z` |
| `(4,12,8)` | globally exact | `4` |
| `(5,13,8)` | globally exact | `5` |
| `(8,24,16)` | globally exact | `8` |

Thus a failure of the global classification does not imply that every
capacity boundary is bad.

## 5. CBS state, transition, and bi-magic loci

For shell parameter `k`, write

\[
G_k(L)=\binom{k+L-1}{k},
\qquad
g_k(L+1)=\binom{k+L-1}{k-1}.
\]

A completed level `L` is

- state-magic when `G_k(L) mod p` lies in `E_{p,h,q}`;
- transition-magic when `g_k(L+1) mod p` lies in `E_{p,h,q}`;
- bi-magic when both conditions hold.

The frozen locus scan used `0 <= L <= 10000`, six width triples, and
`k in {2,3,4,8,16}`, producing 300,030 exact rows.

### 5.1 Non-global triple `(p,h,q)=(5,7,8)`

Counts below are out of 10,001 levels.

| `k` | state | transition | bi |
|---:|---:|---:|---:|
| 2 | 4,001 | 6,000 | 2,000 |
| 3 | 8,001 | 4,000 | 4,000 |
| 4 | 8,001 | 8,000 | 6,000 |
| 8 | 8,401 | 7,600 | 6,400 |
| 16 | 8,401 | 8,000 | 7,200 |

### 5.2 Common-factor non-global triples `(4,6,8)` and `(8,12,16)`

Both produced the same sampled counts.

| `k` | state | transition | bi |
|---:|---:|---:|---:|
| 2 | 5,001 | 5,000 | 2,500 |
| 3 | 7,501 | 5,000 | 5,000 |
| 4 | 5,001 | 7,500 | 3,750 |
| 8 | 5,001 | 8,750 | 4,375 |
| 16 | 4,993 | 9,375 | 4,680 |

The arithmetic defect in these selected non-global triples never exceeded 1.

## 6. Research interpretation

The global exactness relation is now both formally classified and recognized
as prior art in equivalent rounding-function coordinates.  The active research
nucleus is therefore

\[
\boxed{
\{G_k(L),g_k(L+1)\}\bmod p
\quad\cap\quad E_{p,h,q}
}
\]

rather than the global semigroup theorem itself.

The next theorem program is:

1. characterize `E_{p,h,q}` exactly as a union of residue intervals or modular
   inequalities;
2. determine periodicity or automaticity of the CBS binomial sequences modulo
   `p`;
3. prove densities and maximal gaps for state-, transition-, and bi-magic
   levels;
4. identify width triples for which local magic is dense despite global
   non-exactness;
5. only after this arithmetic layer is closed, lift the result to filtered
   matrices and runtime cost.

## 7. Failure recovery retained

The execution encountered and retained, rather than deleting:

- two Lean normalization/proof-orientation repair cycles in the coprime proof;
- two witness-orientation repair cycles in the general-gcd proof;
- a Numba reflected-list typing failure;
- a missing parquet engine, repaired with deterministic CSV-gzip fallback.

These failures changed the next candidates and are recorded in the shared
failure table.

## 8. Claim boundary

This report does not establish:

- novelty of the global classification;
- an asymptotic density theorem for any magic locus;
- bounded waiting gaps beyond the scanned range;
- a matrix-preservation theorem;
- cache, DRAM, NoC, latency, energy, or industrial benefit.
