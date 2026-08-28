# MC G0 Arithmetic Specification v0.1

## Objects

For positive source width `p`, target width `q`, and index `x`, define

\[
I_{p\to q}(x)=\left\lceil\frac{qx}{p}\right\rceil.
\]

For an inserted middle width `h`, define

\[
C_{p,h,q}(x)=I_{h\to q}(I_{p\to h}(x)),
\qquad
\delta_{p,h,q}(x)=C_{p,h,q}(x)-I_{p\to q}(x).
\]

## Theorem ledger

| ID | Lean declaration | Status intended by G0 |
|---|---|---|
| A1 | `paperMagicCount_eq_nextCoffeeBeanShell` | source reconciliation |
| A2 | `coffeeBeanCumulative_corrected` | source reconciliation |
| A3 | `paperMagicCount_eq_cumulativeIncrement` | source reconciliation |
| B1 | `indexLift_le_iff` | exact |
| B2 | `indexLift_spec` | exact |
| B3 | `indexLift_mono` | exact |
| B4 | `indexLift_add_sourceWidth` | exact |
| B5 | `indexLift_le_insertionComposite` | exact |
| B6 | `insertionComposite_eq_direct_of_source_dvd_middle` | exact |
| B7 | `insertionComposite_eq_direct_of_dvd_chain` | exact |
| B8 | `insertionDefect_add_sourceWidth` | exact |

## Immediate mathematical consequences

1. The inserted composite has no negative defect.
2. Exactness needs to be checked on only one residue period
   `x = 0, ..., p-1`.
3. Every source-divisible middle width is exact for every target width and every
   index.
4. Divisor chains are a certified subclass, but not the only possible exact
   subclass.

## Deferred targets

The following remain unproved targets, not current facts:

- a sharp universal upper bound for `δ`;
- the full characterization of triples with `δ(x)=0` for every `x`;
- path-level composition for arbitrary width lists;
- defect polynomials and magic-locus density;
- any cost correspondence to memory transactions or latency.
