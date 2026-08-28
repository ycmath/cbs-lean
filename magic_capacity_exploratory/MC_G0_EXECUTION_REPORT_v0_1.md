# Magic Capacity G0 Execution Report v0.1

**Verdict:** `G0_ARITHMETIC_KERNEL_PASS`  
**Evidence class:** theorem-backed arithmetic only; **not** confirmatory system evidence  
**Generated:** 2026-08-28T22:17:44+09:00

## 1. Provenance

| Field | Value |
|---|---|
| repository | `ycmath/cbs-lean` |
| frozen base branch | `master` |
| frozen base commit | `5234bcec614df2c5658c706ede4705001c774daa` |
| frozen base tree | `1014599ae3f0d8288d778535bca097d1b2ed04cd` |
| exploratory branch | `research/magic-capacity-g0-v0.1-20260828` |
| G0 kernel commit | `74db0b650bcc458f208dcca3b6a82e3492f0ee41` |
| semigroup extension commit | `64ce5864a86fa29ef39ff108e79586a1f519dbc3` |
| semigroup extension tree | `9601933cff4100c7701e31f12e76008e13886469` |
| Lean toolchain | Lean 4 `v4.28.0`, repository-pinned mathlib |
| randomness | none; deterministic theorem checking |
| seed | `null` |

No published paper, frozen theorem file, or `master` ref was overwritten.  New
work lives only on the exploratory branch and under new source/artifact paths.

## 2. G0-A source reconciliation

The new module `CbsLean/MagicCapacity.lean` formalizes that the memory-paper
binomial expression

\[
\binom{k+L-1}{L}
\]

is the zero-indexed shell `coffeeBeanShell k L`, equivalently the *next shell
increment* after `L` completed shells.  It is not the cumulative count

\[
\operatorname{coffeeBeanCumulative}(k,L)
 = \binom{k+L-1}{k}.
\]

Passed declarations:

- `paperMagicCount_eq_nextCoffeeBeanShell`
- `coffeeBeanCumulative_corrected`
- `nextCoffeeBeanShell_eq_cumulativeIncrement`
- `paperMagicCount_eq_cumulativeIncrement`
- `paperMagicCount_dvd_iff_nextShell_dvd`

Interpretation lock: the existing odd-level divisibility result is used in this
research line as a **next-shell insertion-quantum alignment seed**, not as an
already-proved cumulative-state alignment theorem.

## 3. G0-B ceiling-composition kernel

For

\[
I_{p\to q}(x)=\left\lceil\frac{qx}{p}\right\rceil,
\]

and inserted middle width `h`, the module defines

\[
C_{p,h,q}(x)=I_{h\to q}(I_{p\to h}(x)),\qquad
\delta_{p,h,q}(x)=C_{p,h,q}(x)-I_{p\to q}(x).
\]

The compiled theorem spine establishes:

1. `I` is the least feasible lifted index through a ceiling-division Galois
   characterization;
2. `I` is monotone;
3. `I_{p→q}(x+p)=I_{p→q}(x)+q`;
4. direct lifting never exceeds the inserted composite;
5. `δ=0` iff direct and inserted lifts agree;
6. `p | h` is sufficient for exact insertion for every `q,x`;
7. divisor chains are exact;
8. `δ(x+p)=δ(x)`, so one source-width residue period determines the entire
   local defect function.

The core source blob is
`CbsLean/MagicCapacity.lean@79b1ccc99019675b873bcab1f33df5fea49496fc`.

## 4. G0-B+ two-generator strengthening

Execution produced a stronger sufficient condition than the initial divisor
subclass.  If

\[
h=a p+b q\qquad(a,b\in\mathbb N),
\]

then

\[
I_{h\to q}(I_{p\to h}(x))=I_{p\to q}(x)
\quad\text{for every }x.
\]

This is formalized in `CbsLean/MagicCapacitySemigroup.lean` by
`insertionComposite_eq_direct_of_twoGenerator`, with predicate-packaged and
defect-zero corollaries.  The cases `p | h` and `q | h` follow as subclasses.
The source blob is
`CbsLean/MagicCapacitySemigroup.lean@aa1f05c91aa7d5abc486ba595b27fabe40ea6762`.

The converse—global exactness implies `h ∈ ⟨p,q⟩`—remains an exploratory
conjecture.  It is neither a compiled theorem nor a novelty claim.

## 5. Build evidence

| Commit | Workflow run | Job | Lean action | Full workflow at report time |
|---|---:|---:|---|---|
| `74db0b650bcc458f208dcca3b6a82e3492f0ee41` | `33173908021` | `98857510757` | success | docgen in progress |
| `64ce5864a86fa29ef39ff108e79586a1f519dbc3` | `33174427403` | `98859255600` | success | docgen in progress |

The relevant compile gate is the `leanprover/lean-action@v1` step.  Both source
commits passed that step.  The new Lean source contains no explicit `sorry` or
`axiom` declarations.

## 6. Failure recovery

A local-container clone/build path was attempted first, but outbound DNS was
unavailable and no local Lean toolchain was present.  This is an operational
failure, not mathematical evidence.  The deterministic compiler check was
moved to the repository's existing GitHub Actions workflow and succeeded.  The
failure and recovery path are retained in `tables/failure_table.csv`.

## 7. Scope boundaries

Not executed in G0:

- the frozen exhaustive magic-locus grid;
- state-, transition-, or bi-magic density claims;
- filtered block-matrix lifting;
- compiler/runtime cost translation;
- cache, DRAM, NoC, latency, energy, or hardware experiments.

A preliminary targeted literature search did not locate a direct statement of
the two-generator ceiling-composition theorem, but that search was not
systematic enough to support novelty or priority claims.

## 8. Gate disposition

`G0_ARITHMETIC_KERNEL_PASS` authorizes preparation, but not automatic execution,
of the next frozen gate:

1. prior-art search for nested ceiling composition and numerical-semigroup
   characterizations;
2. proof or falsification of the two-generator converse;
3. separately approved exhaustive residue/magic-locus grid;
4. only then, a filtered-matrix lift.
