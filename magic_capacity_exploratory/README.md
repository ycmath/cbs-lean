# Magic Capacity — exploratory G0 line

This directory is an **exploratory research line** built beside, not over, the
published CBS artifacts.  The frozen/public baseline papers and their Lean
formalization remain unchanged on `master`.

## Current execution unit

- G0-A: reconcile cumulative complete-shell capacity with the next-shell
  increment used by the memory-paper alignment formula.
- G0-B: formalize a ceiling-based monotone index lift, local middle-width
  insertion defect, exactness under divisibility, and source-width periodicity.

## Evidence labels

- `theorem-backed`: statements compiled in `CbsLean/MagicCapacity.lean`.
- `exploratory`: finite grids and candidate patterns generated later under
  `outputs/exploratory/`.
- `confirmatory`: reserved; no result in this directory currently has that
  status.

## Frozen source anchor

- repository: `ycmath/cbs-lean`
- source branch: `master`
- source commit: `5234bcec614df2c5658c706ede4705001c774daa`
- source tree: `1014599ae3f0d8288d778535bca097d1b2ed04cd`

## Output discipline

Run configurations belong in `configs/`.  Generated exploratory tables belong
under `outputs/exploratory/`; confirmatory outputs, if later authorized, must use
`outputs/confirmatory/`.  Failed candidates are retained in
`tables/failure_table.csv`.
