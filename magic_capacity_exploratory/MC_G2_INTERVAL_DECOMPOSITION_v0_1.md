# G2 Local-Magic Interval Decomposition v0.1

## Statement

Fix positive widths `p,h,q` and

\[
I_{p\to a}(x)=\left\lceil\frac{ax}{p}\right\rceil.
\]

For a source residue `x` with `1 <= x < p`, put

\[
y=I_{p\to q}(x)\in\{1,\ldots,q\}.
\]

The direct-output condition `I_{p->q}(x)=y` is equivalent to

\[
\left\lfloor\frac{p(y-1)}q\right\rfloor+1
\le x\le
\left\lfloor\frac{py}q\right\rfloor.
\]

By `isLocalMagic_iff_capacityInequality`, local exactness further requires

\[
qI_{p\to h}(x)\le hy.
\]

Since the left side is integral, this is equivalent to

\[
I_{p\to h}(x)\le\left\lfloor\frac{hy}{q}\right\rfloor,
\]

and hence to

\[
x\le
\left\lfloor
\frac p h\left\lfloor\frac{hy}{q}\right\rfloor
\right\rfloor.
\]

The latter upper bound never exceeds `floor(py/q)`.  Therefore the canonical
local-magic residue set is the disjoint union

\[
\boxed{
E_{p,h,q}=\{0\}\cup\bigcup_{y=1}^{q}
\left(
\left[
\left\lfloor\frac{p(y-1)}q\right\rfloor+1,
\min\left(p-1,
\left\lfloor\frac p h\left\lfloor\frac{hy}{q}\right\rfloor\right\rfloor
\right)
\right]\cap\mathbb Z
\right).
}
\]

Empty intervals are omitted.  The union is disjoint because each interval is
contained in a distinct direct-output fiber.

## Cardinality

Consequently

\[
|E_{p,h,q}|=1+\sum_{y=1}^{q}
\max\!\left(
0,
U_y-L_y+1
\right),
\]

where

\[
L_y=\left\lfloor\frac{p(y-1)}q\right\rfloor+1,
\qquad
U_y=\min\left(p-1,
\left\lfloor\frac p h\left\lfloor\frac{hy}{q}\right\rfloor\right\rfloor
\right).
\]

This turns the local zero set from a pointwise residue predicate into a finite
family of integer chambers.  It is useful both for counting and for future
scheduler implementations, where each chamber is an admissible insertion
window in source-index coordinates.

## Example

For `(p,h,q)=(5,7,8)`, only two nonzero chambers survive:

- `y=4`: `[2,2]`;
- `y=7`: `[4,4]`.

Together with `x=0`, this gives

\[
E_{5,7,8}=\{0,2,4\}.
\]

## Deterministic audit

`mc_g2_interval_decomposition_audit_v0_1.py` compared the interval predicate
against direct evaluation of the nested-ceiling defect for

- `1 <= p,q <= 96`,
- `1 <= h <= 192`,
- every `0 <= x < p`.

This covers 1,769,472 width triples.  Mismatches: **0**.

Evidence class: exploratory exact-integer computation.  The interval statement
is mathematically derived above but is not yet promoted to the Lean theorem
surface.

## Prior-art caution

Kulhanek--McDonough--Ponomarenko (2019), *Dilated Floor Functions That Commute
Sometimes*, explicitly studies pointwise commuting sets, their proportions,
and discrepancy bounds for dilated floor maps.  Before claiming novelty for
this chamber decomposition, the precise coordinate translation between their
commuting-set intervals and the present composition-versus-direct set must be
worked out.  Until then this result is treated as an internal structural lemma,
not a novelty claim.
