# MC Research Contract v0.1

**Status:** EXPLORATORY / ACTIVE  
**Execution branch:** `research/magic-capacity-g0-v0.1-20260828`  
**Frozen source commit:** `5234bcec614df2c5658c706ede4705001c774daa`

## Objective order

1. Reconcile the paper-side alignment quantity with the formal CBS shell and
   cumulative-count definitions.
2. Establish a small exact arithmetic kernel for monotone width refinement.
3. Prove local insertion exactness and periodicity before generating any
   empirical magic-locus claims.
4. Only after G0 passes, map state-, transition-, and bi-magic loci on a frozen
   finite grid.
5. Defer filtered-matrix and runtime claims until the arithmetic bridge is
   stable.

## G0-A contract

Formalize:

- `paperMagicCount k L = coffeeBeanShell k L` for `0 < k`;
- `coffeeBeanCumulative k L = choose (k+L-1) k`;
- `paperMagicCount` equals the increment from cumulative level `L` to `L+1`;
- divisibility statements about the paper quantity are therefore next-shell,
  not cumulative-capacity, statements.

## G0-B contract

Define

\[
I_{p\to q}(x)=\left\lceil\frac{qx}{p}\right\rceil
\]

and

\[
\delta_{p,h,q}(x)=I_{h\to q}(I_{p\to h}(x))-I_{p\to q}(x).
\]

Target theorem spine:

- Galois/minimality characterization of `I`;
- monotonicity of `I`;
- `I_{p→q}(x+p)=I_{p→q}(x)+q`;
- direct lift never exceeds the inserted composite;
- source-divisible middle insertion is exact;
- divisor-chain insertion is exact;
- insertion defect is periodic modulo `p`.

## Nonclaims

This execution does **not** claim:

- a hardware theorem;
- reduced cache/DRAM/NoC cost;
- optimal scheduling;
- that every arithmetic magic point is useful at runtime;
- that the published memory paper has already proved cumulative-capacity
  alignment.

## Gates

- G0-PASS: all new Lean declarations compile with zero `sorry` and no new
  axioms.
- G0-FAIL: any target theorem is false or requires a stronger hypothesis; log
  the exact mechanism and retain the weaker residual theorem.
- G1 authority is not implied by this contract; it requires a clean G0 build
  and a new frozen grid config.
