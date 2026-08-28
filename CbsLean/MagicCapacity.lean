import CbsLean.Rigidity
import CbsLean.VWNumerator

namespace CbsLean
namespace MagicCapacity

/-!
# Magic-capacity arithmetic: G0 source reconciliation and local insertion defect

This module is exploratory.  It does not alter the frozen CBS/VW-CBS theorem
claims.  It separates the cumulative complete-shell count from the next-shell
increment, and then defines the ceiling-based width-refinement map used by the
magic-capacity research line.
-/

/--
The binomial quantity currently written as `N^*(L)` in the memory-paper source.
The reconciliation theorems below identify it with the *next shell increment*,
not with the cumulative count through level `L`.
-/
def paperMagicCount (k L : ℕ) : ℕ :=
  Nat.choose (k + L - 1) L

/--
For positive `k`, the paper-side binomial quantity is the zero-indexed CBS shell
`L`, i.e. the paper shell `L + 1`.
-/
theorem paperMagicCount_eq_nextCoffeeBeanShell
    {k L : ℕ} (hk : 0 < k) :
    paperMagicCount k L = coffeeBeanShell k L := by
  unfold paperMagicCount coffeeBeanShell
  have hL : L ≤ k + L - 1 := by omega
  calc
    Nat.choose (k + L - 1) L =
        Nat.choose (k + L - 1) ((k + L - 1) - L) :=
      (Nat.choose_symm hL).symm
    _ = Nat.choose (k + L - 1) (k - 1) := by
      congr 1
      omega

/--
The corrected cumulative complete-shell count.  This is an alias of the
already-formalized closed form in `Rigidity.lean`.
-/
theorem coffeeBeanCumulative_corrected
    {k L : ℕ} (hk : 0 < k) :
    coffeeBeanCumulative k L = Nat.choose (k + L - 1) k :=
  coffeeBeanCumulative_closedForm hk

/-- A shell is the discrete increment between consecutive cumulative counts. -/
theorem nextCoffeeBeanShell_eq_cumulativeIncrement
    {k L : ℕ} :
    coffeeBeanShell k L =
      coffeeBeanCumulative k (L + 1) - coffeeBeanCumulative k L := by
  rw [coffeeBeanCumulative_succ]
  omega

/--
The paper-side binomial quantity is therefore the next cumulative increment.
-/
theorem paperMagicCount_eq_cumulativeIncrement
    {k L : ℕ} (hk : 0 < k) :
    paperMagicCount k L =
      coffeeBeanCumulative k (L + 1) - coffeeBeanCumulative k L := by
  calc
    paperMagicCount k L = coffeeBeanShell k L :=
      paperMagicCount_eq_nextCoffeeBeanShell hk
    _ = coffeeBeanCumulative k (L + 1) - coffeeBeanCumulative k L :=
      nextCoffeeBeanShell_eq_cumulativeIncrement

/-- Divisibility claims for `paperMagicCount` are exactly next-shell claims. -/
theorem paperMagicCount_dvd_iff_nextShell_dvd
    {k L width : ℕ} (hk : 0 < k) :
    width ∣ paperMagicCount k L ↔ width ∣ coffeeBeanShell k L := by
  rw [paperMagicCount_eq_nextCoffeeBeanShell hk]

/--
Monotone width refinement: lift index `x` from `sourceWidth` to
`targetWidth` by the least integer not below the exact rational scaling.
-/
def indexLift (sourceWidth targetWidth x : ℕ) : ℕ :=
  ceilScaled sourceWidth x targetWidth

/-- `indexLift` is ordinary natural-number ceiling division. -/
theorem indexLift_eq_ceilDiv
    {sourceWidth targetWidth x : ℕ} :
    indexLift sourceWidth targetWidth x =
      (targetWidth * x) ⌈/⌉ sourceWidth := by
  rfl

/-- Galois characterization: the lifted index is the least feasible target index. -/
theorem indexLift_le_iff
    {sourceWidth targetWidth x y : ℕ}
    (hsource : 0 < sourceWidth) :
    indexLift sourceWidth targetWidth x ≤ y ↔
      targetWidth * x ≤ sourceWidth * y := by
  rw [indexLift_eq_ceilDiv]
  exact ceilDiv_le_iff_le_mul hsource

/-- Every lift satisfies its defining capacity inequality. -/
theorem indexLift_spec
    {sourceWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth) :
    targetWidth * x ≤
      sourceWidth * indexLift sourceWidth targetWidth x :=
  (indexLift_le_iff hsource).1 le_rfl

/-- The index lift is monotone in its index argument. -/
theorem indexLift_mono
    {sourceWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth) :
    Monotone (indexLift sourceWidth targetWidth) := by
  intro x y hxy
  apply (indexLift_le_iff hsource).2
  exact
    (Nat.mul_le_mul_left targetWidth hxy).trans
      (indexLift_spec
        (sourceWidth := sourceWidth)
        (targetWidth := targetWidth)
        (x := y) hsource)

/-- When the source width divides the target width, refinement is exact scaling. -/
theorem indexLift_eq_of_dvd
    {sourceWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hdiv : sourceWidth ∣ targetWidth) :
    indexLift sourceWidth targetWidth x =
      (targetWidth / sourceWidth) * x := by
  simpa [indexLift] using
    (ceilScaled_eq_of_dvd
      (prevWidth := sourceWidth)
      (acc := x)
      (currWidth := targetWidth)
      hsource hdiv)

/-- Refining by one full source-width period adds exactly one target width. -/
theorem indexLift_add_sourceWidth
    {sourceWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth) :
    indexLift sourceWidth targetWidth (x + sourceWidth) =
      indexLift sourceWidth targetWidth x + targetWidth := by
  unfold indexLift ceilScaled
  have hsource1 : 1 ≤ sourceWidth := Nat.succ_le_of_lt hsource
  have hnum :
      targetWidth * (x + sourceWidth) + sourceWidth - 1 =
        (targetWidth * x + sourceWidth - 1) +
          targetWidth * sourceWidth := by
    calc
      targetWidth * (x + sourceWidth) + sourceWidth - 1 =
          (targetWidth * x + targetWidth * sourceWidth) + sourceWidth - 1 := by
        rw [Nat.mul_add]
      _ = targetWidth * x + targetWidth * sourceWidth + (sourceWidth - 1) := by
        rw [Nat.add_sub_assoc hsource1]
      _ = targetWidth * x + (sourceWidth - 1) + targetWidth * sourceWidth := by
        ac_rfl
      _ = (targetWidth * x + sourceWidth - 1) +
          targetWidth * sourceWidth := by
        rw [Nat.add_sub_assoc hsource1]
  rw [hnum, Nat.add_mul_div_right _ _ hsource]

/-- The two-step index obtained after inserting a middle width. -/
def insertionComposite (sourceWidth middleWidth targetWidth x : ℕ) : ℕ :=
  indexLift middleWidth targetWidth
    (indexLift sourceWidth middleWidth x)

/--
The local insertion defect.  The theorem `indexLift_le_insertionComposite`
proves that this natural subtraction is a genuine nonnegative excess.
-/
def insertionDefect (sourceWidth middleWidth targetWidth x : ℕ) : ℕ :=
  insertionComposite sourceWidth middleWidth targetWidth x -
    indexLift sourceWidth targetWidth x

/-- Inserting a ceiling-refinement stage cannot undershoot the direct lift. -/
theorem indexLift_le_insertionComposite
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    indexLift sourceWidth targetWidth x ≤
      insertionComposite sourceWidth middleWidth targetWidth x := by
  apply (indexLift_le_iff hsource).2
  have hinner :
      middleWidth * x ≤
        sourceWidth * indexLift sourceWidth middleWidth x :=
    indexLift_spec
      (sourceWidth := sourceWidth)
      (targetWidth := middleWidth)
      (x := x) hsource
  have houter :
      targetWidth * indexLift sourceWidth middleWidth x ≤
        middleWidth * insertionComposite sourceWidth middleWidth targetWidth x := by
    simpa [insertionComposite] using
      (indexLift_spec
        (sourceWidth := middleWidth)
        (targetWidth := targetWidth)
        (x := indexLift sourceWidth middleWidth x) hmiddle)
  have hscaled :
      middleWidth * (targetWidth * x) ≤
        middleWidth *
          (sourceWidth * insertionComposite sourceWidth middleWidth targetWidth x) := by
    calc
      middleWidth * (targetWidth * x) =
          targetWidth * (middleWidth * x) := by ac_rfl
      _ ≤ targetWidth *
          (sourceWidth * indexLift sourceWidth middleWidth x) :=
        Nat.mul_le_mul_left targetWidth hinner
      _ = sourceWidth *
          (targetWidth * indexLift sourceWidth middleWidth x) := by ac_rfl
      _ ≤ sourceWidth *
          (middleWidth * insertionComposite sourceWidth middleWidth targetWidth x) :=
        Nat.mul_le_mul_left sourceWidth houter
      _ = middleWidth *
          (sourceWidth * insertionComposite sourceWidth middleWidth targetWidth x) := by
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled hmiddle

/-- Zero defect is equivalent to exact equality of direct and inserted lifts. -/
theorem insertionDefect_eq_zero_iff
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    insertionDefect sourceWidth middleWidth targetWidth x = 0 ↔
      insertionComposite sourceWidth middleWidth targetWidth x =
        indexLift sourceWidth targetWidth x := by
  have hle :
      indexLift sourceWidth targetWidth x ≤
        insertionComposite sourceWidth middleWidth targetWidth x :=
    indexLift_le_insertionComposite hsource hmiddle
  constructor
  · intro hzero
    apply Nat.le_antisymm
    · exact (Nat.sub_eq_zero_iff_le).mp hzero
    · exact hle
  · intro heq
    simp [insertionDefect, heq]

/--
A divisor chain gives exact associativity of width refinement.
-/
theorem insertionComposite_eq_direct_of_dvd_chain
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (hsourceMiddle : sourceWidth ∣ middleWidth)
    (hmiddleTarget : middleWidth ∣ targetWidth) :
    insertionComposite sourceWidth middleWidth targetWidth x =
      indexLift sourceWidth targetWidth x := by
  calc
    insertionComposite sourceWidth middleWidth targetWidth x =
        (targetWidth / middleWidth) *
          indexLift sourceWidth middleWidth x := by
      simpa [insertionComposite] using
        (indexLift_eq_of_dvd
          (sourceWidth := middleWidth)
          (targetWidth := targetWidth)
          (x := indexLift sourceWidth middleWidth x)
          hmiddle hmiddleTarget)
    _ = (targetWidth / middleWidth) *
        ((middleWidth / sourceWidth) * x) := by
      rw [indexLift_eq_of_dvd hsource hsourceMiddle]
    _ = ((middleWidth / sourceWidth) *
        (targetWidth / middleWidth)) * x := by ac_rfl
    _ = (targetWidth / sourceWidth) * x := by
      rw [quotient_mul_quotient_eq_quotient
        hsource hmiddle hsourceMiddle hmiddleTarget]
    _ = indexLift sourceWidth targetWidth x := by
      symm
      exact indexLift_eq_of_dvd hsource
        (dvd_trans hsourceMiddle hmiddleTarget)

/--
The stronger one-sided exactness law: it is enough that the source width divide
the inserted middle width; the target need not be in the divisor chain.
-/
theorem insertionComposite_eq_direct_of_source_dvd_middle
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (hsourceMiddle : sourceWidth ∣ middleWidth) :
    insertionComposite sourceWidth middleWidth targetWidth x =
      indexLift sourceWidth targetWidth x := by
  apply Nat.le_antisymm
  · apply (indexLift_le_iff hmiddle).2
    rw [indexLift_eq_of_dvd hsource hsourceMiddle]
    have hdirect :
        targetWidth * x ≤
          sourceWidth * indexLift sourceWidth targetWidth x :=
      indexLift_spec
        (sourceWidth := sourceWidth)
        (targetWidth := targetWidth)
        (x := x) hsource
    have hmul := Nat.mul_le_mul_left (middleWidth / sourceWidth) hdirect
    calc
      targetWidth * ((middleWidth / sourceWidth) * x) =
          (middleWidth / sourceWidth) * (targetWidth * x) := by ac_rfl
      _ ≤ (middleWidth / sourceWidth) *
          (sourceWidth * indexLift sourceWidth targetWidth x) := hmul
      _ = middleWidth * indexLift sourceWidth targetWidth x := by
        rw [← Nat.mul_assoc, Nat.div_mul_cancel hsourceMiddle]
  · exact indexLift_le_insertionComposite hsource hmiddle

/-- Source-divisible insertion is carry-free. -/
theorem insertionDefect_eq_zero_of_source_dvd_middle
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (hsourceMiddle : sourceWidth ∣ middleWidth) :
    insertionDefect sourceWidth middleWidth targetWidth x = 0 := by
  apply (insertionDefect_eq_zero_iff hsource hmiddle).2
  exact insertionComposite_eq_direct_of_source_dvd_middle
    hsource hmiddle hsourceMiddle

/-- Divisor-chain insertion is carry-free. -/
theorem insertionDefect_eq_zero_of_dvd_chain
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (hsourceMiddle : sourceWidth ∣ middleWidth)
    (hmiddleTarget : middleWidth ∣ targetWidth) :
    insertionDefect sourceWidth middleWidth targetWidth x = 0 := by
  apply (insertionDefect_eq_zero_iff hsource hmiddle).2
  exact insertionComposite_eq_direct_of_dvd_chain
    hsource hmiddle hsourceMiddle hmiddleTarget

/-- The inserted composite inherits the source-width period. -/
theorem insertionComposite_add_sourceWidth
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    insertionComposite sourceWidth middleWidth targetWidth (x + sourceWidth) =
      insertionComposite sourceWidth middleWidth targetWidth x + targetWidth := by
  unfold insertionComposite
  rw [indexLift_add_sourceWidth
    (sourceWidth := sourceWidth)
    (targetWidth := middleWidth)
    (x := x) hsource]
  rw [indexLift_add_sourceWidth
    (sourceWidth := middleWidth)
    (targetWidth := targetWidth)
    (x := indexLift sourceWidth middleWidth x) hmiddle]

/-- The local insertion defect is periodic modulo the source width. -/
theorem insertionDefect_add_sourceWidth
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    insertionDefect sourceWidth middleWidth targetWidth (x + sourceWidth) =
      insertionDefect sourceWidth middleWidth targetWidth x := by
  unfold insertionDefect
  rw [insertionComposite_add_sourceWidth hsource hmiddle]
  rw [indexLift_add_sourceWidth
    (sourceWidth := sourceWidth)
    (targetWidth := targetWidth)
    (x := x) hsource]
  omega

/-- Predicate for an exact local magic insertion. -/
def IsInsertionMagic
    (sourceWidth middleWidth targetWidth x : ℕ) : Prop :=
  insertionDefect sourceWidth middleWidth targetWidth x = 0

/-- Magic insertion is periodic modulo the source width. -/
theorem isInsertionMagic_add_sourceWidth_iff
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    IsInsertionMagic sourceWidth middleWidth targetWidth (x + sourceWidth) ↔
      IsInsertionMagic sourceWidth middleWidth targetWidth x := by
  simp only [IsInsertionMagic, insertionDefect_add_sourceWidth hsource hmiddle]

end MagicCapacity
end CbsLean
