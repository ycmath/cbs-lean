# MC Source Reconciliation v0.1

## Two distinct quantities

With zero-indexed Lean shell index `i`,

\[
g_k(i)=\binom{k+i-1}{k-1}.
\]

The cumulative count through `L` shells is

\[
G_k(L)=\sum_{i=0}^{L-1}g_k(i)=\binom{k+L-1}{k}.
\]

The paper-side expression

\[
\binom{k+L-1}{L}=\binom{k+L-1}{k-1}
\]

is instead

\[
g_k(L),
\]

which is the next shell after the first `L` shells have been completed.

## Formal consequences

`CbsLean/MagicCapacity.lean` records:

- `paperMagicCount_eq_nextCoffeeBeanShell`;
- `coffeeBeanCumulative_corrected`;
- `nextCoffeeBeanShell_eq_cumulativeIncrement`;
- `paperMagicCount_eq_cumulativeIncrement`;
- `paperMagicCount_dvd_iff_nextShell_dvd`.

## Interpretation lock

Until a separate cumulative divisibility theorem is proved, the existing
odd-level power-of-two result is used only as a **next-shell insertion-quantum
alignment seed**.  It is not cited as a theorem that the whole cumulative state
is width aligned.

This note changes no published artifact.  It governs the new exploratory line
only.
