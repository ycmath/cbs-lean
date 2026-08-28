# Magic Capacity G2 Local-Magic Report v0.1

**Status:** exploratory arithmetic / theorem-development stage  
**Base:** `research/magic-capacity-g1-characterization-v0.1-20260828@8deb71d16050753dc15eda85135fae23b0095789`  
**Branch:** `research/magic-capacity-g2-local-locus-v0.1-20260829`

## 1. Repositioned objective

G1 closed the global exact-insertion problem:

\[
I_{h\to q}(I_{p\to h}(x))=I_{p\to q}(x)\ \forall x
\iff h\in\langle p,q\rangle,
\]

but this classification is prior-art adjacent/reducible to the Lagarias--Richman
dilated-floor-function program.  G2 therefore studies the *local* zero-defect
set for a fixed, potentially non-global triple:

\[
E_{p,h,q}:=\{x\bmod p:\delta_{p,h,q}(x)=0\}.
\]

The systems question becomes whether CBS shell-completion and next-shell
sequences visit `E_{p,h,q}` often enough, and with bounded waiting gaps, to make
reconfiguration scheduling useful.

## 2. Exact local criterion

Let

\[
I_{p\to a}(x)=\left\lceil\frac{ax}{p}\right\rceil.
\]

Because the direct lift is always no larger than the inserted composite, local
exactness is equivalent to the reverse capacity inequality

\[
\boxed{
\delta_{p,h,q}(x)=0
\iff
q I_{p\to h}(x)\le h I_{p\to q}(x).
}
\]

This statement is formalized in `CbsLean/MagicCapacityLocal.lean` as
`isLocalMagic_iff_capacityInequality`.

Define the ceiling residual

\[
r_a(x):=p I_{p\to a}(x)-ax\in\{0,\ldots,p-1\}.
\]

Algebraically the same criterion is

\[
\boxed{q r_h(x)\le h r_q(x).}
\]

Thus `E_{p,h,q}` is a finite modular chamber cut out by a comparison of two
sawtooth residual functions.  The residual version is currently a paper-side
lemma target; the capacity-inequality form is already Lean-checked once CI
passes.

## 3. Periodicity and finite certification

G0 already proved

\[
\delta_{p,h,q}(x+p)=\delta_{p,h,q}(x).
\]

Therefore one complete source residue period `0 <= x < p` exactly determines
all local-magic indices.  `MagicCapacityLocal.lean` packages the canonical
finite set as `localMagicResidues`.

Common scaling also leaves the complete defect function unchanged:

\[
\delta_{dp,dh,dq}(x)=\delta_{p,h,q}(x).
\]

A deterministic scan checked this for `1<=p,q<=32`, `1<=h<=64`, and
`d in {2,3,5}` with zero mismatches.

## 4. Deterministic local-criterion audit

`mc_g2_local_locus_scan_v0_2.py` exhaustively checked

- `1 <= p,q <= 64`,
- `1 <= h <= 128`,
- every source residue `0 <= x < p`.

This is 524,288 width triples.  The residual criterion
`q*r_h <= h*r_q` disagreed with direct zero-defect evaluation in **0 cases**.
The largest defect observed anywhere in this audit was 63.

This is exploratory computational evidence supporting the exact algebraic
criterion, not hardware evidence.

## 5. CBS orbit periodicity

For fixed shell dimension `k`, the two CBS quantities are

\[
G_k(L)=\binom{k+L-1}{k},\qquad
T_k(L)=g_k(L+1)=\binom{k+L-1}{k-1}.
\]

Modulo the source width `p`, both are purely periodic.  A convenient state-space
proof uses the Pascal row vector and the invertible unipotent Pascal update
matrix modulo `p`.

More sharply, this periodicity is classical prior art.  Kwong's 1989 minimum
period result for fixed-lower-index binomial coefficients modulo an arbitrary
modulus gives, for `r>0`,

\[
\Pi_m(r)
=\prod_{\ell^a\parallel m}
  \ell^{a+\lfloor\log_\ell r\rfloor}.
\]

Consequently:

\[
\operatorname{per}(G_k\bmod p)=\Pi_p(k),\qquad
\operatorname{per}(T_k\bmod p)=\Pi_p(k-1).
\]

Since `Pi_p(k-1)` divides `Pi_p(k)`, the joint `(state,transition)` residue orbit
has period dividing `Pi_p(k)` (and in the tested examples equals it).

`mc_g2_kwong_period_audit_v0_1.py` independently reconstructed the minimum
period by Pascal recurrence for every modulus `2..64` and lower index `1..32`:
2,016 pairs, **0 mismatches** with the Kwong formula.

Therefore state-, transition-, and bi-magic are not merely asymptotically
regular: they are exactly periodic finite-state predicates.  Their exact density
and cyclic maximum waiting gap are computable from one period.

## 6. Representative exact densities and waiting gaps

For `(p,h,q)=(5,7,8)`,

\[
E_{5,7,8}=\{0,2,4\}.
\]

The exact one-cycle results are:

| k | joint period | state density | transition density | bi density | max bi non-magic run |
|---:|---:|---:|---:|---:|---:|
| 2 | 5 | 0.40 | 0.60 | 0.20 | 4 |
| 3 | 5 | 0.80 | 0.40 | 0.40 | 3 |
| 4 | 5 | 0.80 | 0.80 | 0.60 | 2 |
| 5 | 25 | 0.60 | 0.80 | 0.48 | 6 |
| 8 | 25 | 0.84 | 0.76 | 0.64 | 3 |
| 16 | 25 | 0.84 | 0.80 | 0.72 | 5 |

This upgrades the earlier finite-window observation `0<=L<=10000`: the values
above are exact periodic densities for the model.

For `(4,6,8)` and its common scaling `(8,12,16)`, the local sets are
`{0,2}` and `{0,2,4,6}` respectively.  The magic densities are identical under
the natural scaling, while the raw binomial residue periods scale with the
modulus.  This separates two structures that had been conflated in the first
finite scan: local-defect scaling invariance versus CBS residue-orbit period.

## 7. Prior-art boundary

Two nearby literatures must remain explicit:

1. Lagarias--Murayama--Richman and Lagarias--Richman classify global
   commutation/nonnegative-commutator phenomena for dilated floor functions,
   with strong connections to Beatty sequences and two-generator Frobenius
   semigroups.
2. Kulhanek--McDonough--Ponomarenko (2019), *Dilated Floor Functions That
   Commute Sometimes*, studies the set of input points where two dilated floor
   functions commute, including domain proportions and discrepancy bounds.
3. Kwong (1989), *Minimum Periods of Binomial Coefficients Modulo M*, supplies
   the minimum-period theory for the CBS binomial residue sequences.

Accordingly, no novelty claim is made for local zero sets of generic nested
floor/ceiling maps or for binomial periodicity in isolation.

The potentially distinct research object is the **coupled intersection**

\[
\boxed{
E_{p,h,q}
\cap
\{G_k(L),\ g_k(L+1)\pmod p\}
}
\]

together with a compute--memory--signal interpretation in which a visit to the
intersection permits a semantics-preserving low-reconfiguration-cost block
insertion.

## 8. Next theorem gate

The next gate is deliberately narrower than a matrix implementation:

1. formalize the residual criterion `q*r_h <= h*r_q`;
2. derive an explicit chamber/interval decomposition of `E_{p,h,q}` and its
   cardinality, while auditing against the 2019 "commute sometimes" literature;
3. import or reprove only the minimum amount of binomial-period theory needed
   to certify exact magic density and maximum waiting gap;
4. classify when bi-magic is empty, positive-density, or high-density;
5. only after these are stable, lift the contract to filtered block matrices.

No cache/DRAM/NoC/latency/energy claim is authorized by G2 arithmetic alone.
