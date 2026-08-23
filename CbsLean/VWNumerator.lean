import Mathlib

namespace CbsLean

/--
`digitBox K` encodes the digit vectors `b` with `0 ≤ b_i < k_i` as a finset of
lists aligned with the width list `K`.

This is the finite indexing set that appears in the VW-CBS mixed-radix
numerator formulas.
-/
def digitBox : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | k :: ks =>
      ((Finset.range k).product (digitBox ks)).image fun p => p.1 :: p.2

/--
The arithmetic core of the VW-CBS recurrence:

`ceilScaled prevWidth acc currWidth` is the integer ceiling of
`(currWidth / prevWidth) * acc`, written in a division-free natural-number form.
-/
def ceilScaled (prevWidth acc currWidth : ℕ) : ℕ :=
  (currWidth * acc + prevWidth - 1) / prevWidth

/--
One mixed-radix update step for the recurrence `A_i`.
-/
def mixedRadixStep (prevWidth acc currWidth digit : ℕ) : ℕ :=
  digit + ceilScaled prevWidth acc currWidth

/--
Iterate the mixed-radix recurrence across a list of subsequent
`(width, digit)` pairs.
-/
def mixedRadixAux (prevWidth acc : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => acc
  | (currWidth, digit) :: rest =>
      mixedRadixAux currWidth (mixedRadixStep prevWidth acc currWidth digit) rest

/--
Full mixed-radix recurrence, packaged as a nonempty list of `(width, digit)`
pairs.
-/
def mixedRadixFromPairs : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (width, digit) :: rest => mixedRadixAux width digit rest

/--
The last width appearing in a mixed-radix chain.
-/
def finalWidth {α : Type} (startWidth : ℕ) : List (ℕ × α) → ℕ
  | [] => startWidth
  | (currWidth, _) :: rest => finalWidth currWidth rest

/--
Given a fixed final width, sum the weighted digit contributions
`digit * (finalWidth / width)`.
-/
def weightedDigitSum (lastWidth : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (width, digit) :: rest =>
      digit * (lastWidth / width) + weightedDigitSum lastWidth rest

/--
`ChainDividesFrom prevWidth steps` means each width in the chain is divisible by
the previous one.
-/
def ChainDividesFrom {α : Type} (prevWidth : ℕ) : List (ℕ × α) → Prop
  | [] => True
  | (currWidth, _) :: rest =>
      prevWidth ∣ currWidth ∧ ChainDividesFrom currWidth rest

/--
All widths occurring in the chain are positive.
-/
def PositiveWidths {α : Type} : List (ℕ × α) → Prop
  | [] => True
  | (width, _) :: rest => 0 < width ∧ PositiveWidths rest

/--
Pair a width list and a digit list in the manuscript style.
-/
def widthDigitPairs (widths digits : List ℕ) : List (ℕ × ℕ) :=
  List.zip widths digits

/--
The last width in a manuscript-style width list.
-/
def finalWidthOfWidths (startWidth : ℕ) : List ℕ → ℕ
  | [] => startWidth
  | currWidth :: rest => finalWidthOfWidths currWidth rest

/--
The closed numerator exponent attached to the final mixed-radix value.
-/
def closedExponent (lastWidth lastValue : ℕ) : ℕ :=
  (lastValue + lastWidth - 1) / lastWidth

/--
The half-open numerator exponent attached to the final mixed-radix value.
-/
def halfOpenExponent (lastWidth lastValue : ℕ) : ℕ :=
  lastValue / lastWidth + 1

/--
The step payload that remains after extracting the previous quotient part.
-/
def carryPayload (prevWidth prevValue currWidth digit : ℕ) : ℕ :=
  digit + ceilScaled prevWidth (prevValue % prevWidth) currWidth

/--
The carry increment at one mixed-radix step.
-/
def carryIncrement (prevWidth prevValue currWidth digit : ℕ) : ℕ :=
  carryPayload prevWidth prevValue currWidth digit / currWidth

/--
Accumulate carry increments along a mixed-radix chain.
-/
def carryCountAux (prevWidth prevValue : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (currWidth, digit) :: rest =>
      carryIncrement prevWidth prevValue currWidth digit +
        carryCountAux currWidth (mixedRadixStep prevWidth prevValue currWidth digit) rest

/--
Wrapper matching manuscript notation: evaluate the recurrence from separate
width and digit lists.
-/
def mixedRadixValue : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | width :: widths, digit :: digits =>
      mixedRadixAux width digit (widthDigitPairs widths digits)

/--
Wrapper matching manuscript notation: count carries from separate width and
digit lists.
-/
def carryCountValue : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | width :: widths, digit :: digits =>
      carryCountAux width digit (widthDigitPairs widths digits)

/--
Digit-box wrapper for the total carry count attached to a nonempty width list.
-/
def digitBoxCarryCount (startWidth : ℕ) (restWidths : List ℕ) : List ℕ → ℕ
  | [] => 0
  | startDigit :: restDigits =>
      carryCountValue (startWidth :: restWidths) (startDigit :: restDigits)

/--
Digit-box wrapper for the final mixed-radix value `A_m(b)` attached to a
nonempty width list.
-/
def digitBoxLastValue (startWidth : ℕ) (restWidths : List ℕ) : List ℕ → ℕ
  | [] => 0
  | startDigit :: restDigits =>
      mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits)

/--
Digit-box wrapper for the closed exponent attached to a nonempty width list.
-/
def digitBoxClosedExponent (startWidth : ℕ) (restWidths : List ℕ) : List ℕ → ℕ
  | [] => 0
  | startDigit :: restDigits =>
      closedExponent (finalWidthOfWidths startWidth restWidths)
        (digitBoxLastValue startWidth restWidths (startDigit :: restDigits))

/--
Digit-box wrapper for the half-open exponent attached to a nonempty width list.
-/
def digitBoxHalfOpenExponent (startWidth : ℕ) (restWidths : List ℕ) : List ℕ → ℕ
  | [] => 0
  | startDigit :: restDigits =>
      halfOpenExponent (finalWidthOfWidths startWidth restWidths)
        (mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits))

/--
Shared label for the closed and half-open VW-CBS numerator families.
-/
inductive NumeratorKind where
  | closed
  | halfOpen
  deriving DecidableEq, Repr

/--
Shared digit-box exponent map for the VW-CBS numerator families.
-/
def digitBoxNumeratorExponent
    (kind : NumeratorKind) (startWidth : ℕ) (restWidths : List ℕ) : List ℕ → ℕ :=
  match kind with
  | .closed => digitBoxClosedExponent startWidth restWidths
  | .halfOpen => digitBoxHalfOpenExponent startWidth restWidths

/--
`etaCoeff startWidth restWidths j` is the size of the exponent-`j` fiber over the
digit box for the width vector `startWidth :: restWidths`.
-/
def etaCoeff (startWidth : ℕ) (restWidths : List ℕ) (j : ℕ) : ℕ :=
  ((digitBox (startWidth :: restWidths)).filter fun digits =>
    digitBoxHalfOpenExponent startWidth restWidths digits = j).card

/--
`hStarCoeff startWidth restWidths j` is the size of the closed exponent-`j`
fiber over the digit box for the width vector `startWidth :: restWidths`.
-/
def hStarCoeff (startWidth : ℕ) (restWidths : List ℕ) (j : ℕ) : ℕ :=
  ((digitBox (startWidth :: restWidths)).filter fun digits =>
    digitBoxClosedExponent startWidth restWidths digits = j).card

/--
Shared coefficient family for the closed and half-open VW-CBS numerators.
-/
def numeratorCoeff
    (kind : NumeratorKind) (startWidth : ℕ) (restWidths : List ℕ) (j : ℕ) : ℕ :=
  ((digitBox (startWidth :: restWidths)).filter fun digits =>
    digitBoxNumeratorExponent kind startWidth restWidths digits = j).card

/--
Polynomial object attached to the closed or half-open VW-CBS numerator family.

It is defined directly as the digit-box sum of monomials `X^e`, so its
coefficient extraction is exactly the current `numeratorCoeff` API.
-/
noncomputable def numeratorPolynomial
    (kind : NumeratorKind) (startWidth : ℕ) (restWidths : List ℕ) : Polynomial ℕ :=
  Finset.sum (digitBox (startWidth :: restWidths)) fun digits =>
    Polynomial.X ^ digitBoxNumeratorExponent kind startWidth restWidths digits

/--
Closed numerator polynomial `h_K^*(z)` in Lean-facing form.
-/
noncomputable def hStarPolynomial (startWidth : ℕ) (restWidths : List ℕ) : Polynomial ℕ :=
  numeratorPolynomial NumeratorKind.closed startWidth restWidths

/--
Half-open numerator polynomial `η_K(z)` in Lean-facing form.
-/
noncomputable def etaPolynomial (startWidth : ℕ) (restWidths : List ℕ) : Polynomial ℕ :=
  numeratorPolynomial NumeratorKind.halfOpen startWidth restWidths

@[simp] theorem digitBoxNumeratorExponent_closed
    {startWidth : ℕ} {restWidths digits : List ℕ} :
    digitBoxNumeratorExponent NumeratorKind.closed startWidth restWidths digits =
      digitBoxClosedExponent startWidth restWidths digits := rfl

@[simp] theorem digitBoxNumeratorExponent_halfOpen
    {startWidth : ℕ} {restWidths digits : List ℕ} :
    digitBoxNumeratorExponent NumeratorKind.halfOpen startWidth restWidths digits =
      digitBoxHalfOpenExponent startWidth restWidths digits := rfl

@[simp] theorem numeratorCoeff_closed_eq_hStarCoeff
    {startWidth : ℕ} {restWidths : List ℕ} {j : ℕ} :
    numeratorCoeff NumeratorKind.closed startWidth restWidths j =
      hStarCoeff startWidth restWidths j := rfl

@[simp] theorem numeratorCoeff_halfOpen_eq_etaCoeff
    {startWidth : ℕ} {restWidths : List ℕ} {j : ℕ} :
    numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
      etaCoeff startWidth restWidths j := rfl

@[simp] theorem coeff_numeratorPolynomial
    {kind : NumeratorKind} {startWidth j : ℕ} {restWidths : List ℕ} :
    Polynomial.coeff (numeratorPolynomial kind startWidth restWidths) j =
      numeratorCoeff kind startWidth restWidths j := by
  classical
  rw [numeratorPolynomial, numeratorCoeff, Polynomial.finset_sum_coeff]
  calc
    ∑ digits ∈ digitBox (startWidth :: restWidths),
        Polynomial.coeff
          (Polynomial.X ^ digitBoxNumeratorExponent kind startWidth restWidths digits) j
      =
        ∑ digits ∈ digitBox (startWidth :: restWidths),
          if digitBoxNumeratorExponent kind startWidth restWidths digits = j then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro digits hdigits
          rw [Polynomial.coeff_X_pow]
          simp [eq_comm]
    _ = ((digitBox (startWidth :: restWidths)).filter fun digits =>
          digitBoxNumeratorExponent kind startWidth restWidths digits = j).card := by
          symm
          calc
            ((digitBox (startWidth :: restWidths)).filter fun digits =>
                digitBoxNumeratorExponent kind startWidth restWidths digits = j).card
              =
                ∑ _digits ∈ (digitBox (startWidth :: restWidths)).filter fun digits =>
                    digitBoxNumeratorExponent kind startWidth restWidths digits = j, 1 := by
                  exact Finset.card_eq_sum_ones _
            _ =
                ∑ digits ∈ digitBox (startWidth :: restWidths),
                  if digitBoxNumeratorExponent kind startWidth restWidths digits = j then
                    1
                  else
                    0 := by
                  rw [Finset.sum_filter]

@[simp] theorem coeff_hStarPolynomial
    {startWidth j : ℕ} {restWidths : List ℕ} :
    Polynomial.coeff (hStarPolynomial startWidth restWidths) j =
      hStarCoeff startWidth restWidths j := by
  simp [hStarPolynomial]

@[simp] theorem coeff_etaPolynomial
    {startWidth j : ℕ} {restWidths : List ℕ} :
    Polynomial.coeff (etaPolynomial startWidth restWidths) j =
      etaCoeff startWidth restWidths j := by
  simp [etaPolynomial]

theorem mem_digitBox_length
    {widths digits : List ℕ}
    (hmem : digits ∈ digitBox widths) :
    digits.length = widths.length := by
  induction widths generalizing digits with
  | nil =>
      simpa [digitBox] using hmem
  | cons width widths ih =>
      cases digits with
      | nil =>
          simp [digitBox] at hmem
      | cons digit digits =>
          have hmem' : digit < width ∧ digits ∈ digitBox widths := by
            simpa [digitBox] using hmem
          rcases hmem' with ⟨hdigit, htail⟩
          simp [ih htail]

theorem mem_digitBox_forall₂_lt
    {widths digits : List ℕ}
    (hmem : digits ∈ digitBox widths) :
    List.Forall₂ (fun digit width => digit < width) digits widths := by
  induction widths generalizing digits with
  | nil =>
      cases digits <;> simp [digitBox] at hmem ⊢
  | cons width widths ih =>
      cases digits with
      | nil =>
          simp [digitBox] at hmem
      | cons digit digits =>
          have hmem' : digit < width ∧ digits ∈ digitBox widths := by
            simpa [digitBox] using hmem
          rcases hmem' with ⟨hdigit, htail⟩
          exact List.Forall₂.cons hdigit (ih htail)

theorem positiveWidths_widthDigitPairs_of_forall_pos
    {widths digits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) widths) :
    PositiveWidths (widthDigitPairs widths digits) := by
  induction widths generalizing digits with
  | nil =>
      simp [widthDigitPairs, PositiveWidths]
  | cons width widths ih =>
      cases digits with
      | nil =>
          simp [widthDigitPairs, PositiveWidths]
      | cons digit digits =>
          have hpos' : 0 < width ∧ List.Forall (fun width => 0 < width) widths := by
            simpa using hpos
          rcases hpos' with ⟨hwidth, hposTail⟩
          have htail : PositiveWidths (widthDigitPairs widths digits) := ih hposTail
          simpa [widthDigitPairs, PositiveWidths, hwidth] using htail

theorem halfOpenExponent_pos {lastWidth lastValue : ℕ} :
    1 ≤ halfOpenExponent lastWidth lastValue := by
  simp [halfOpenExponent]

theorem halfOpenExponent_eq_iff_interval
    {lastWidth lastValue j : ℕ}
    (hwidth : 0 < lastWidth) :
    halfOpenExponent lastWidth lastValue = j ↔
      (j - 1) * lastWidth ≤ lastValue ∧ lastValue < j * lastWidth := by
  cases j with
  | zero =>
      constructor
      · intro h
        have hge : 1 ≤ halfOpenExponent lastWidth lastValue := halfOpenExponent_pos
        omega
      · intro h
        rcases h with ⟨hlower, hupper⟩
        simp at hupper
  | succ j =>
      constructor
      · intro h
        have hquot : lastValue / lastWidth = j := by
          simpa [halfOpenExponent] using Nat.succ.inj h
        constructor
        · exact (Nat.le_div_iff_mul_le hwidth).1 (by simp [hquot])
        · have hlt : lastValue / lastWidth < j + 1 := by
            simp [hquot]
          exact (Nat.div_lt_iff_lt_mul hwidth).1 hlt
      · intro h
        rcases h with ⟨hlower, hupper⟩
        have hle : lastValue / lastWidth ≤ j := by
          exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hwidth).2 hupper)
        have hge : j ≤ lastValue / lastWidth := by
          exact (Nat.le_div_iff_mul_le hwidth).2 hlower
        have hquot : lastValue / lastWidth = j := le_antisymm hle hge
        simp [halfOpenExponent, hquot]

theorem closedExponent_succ_eq_halfOpenExponent
    {lastWidth n : ℕ}
    (hwidth : 0 < lastWidth) :
    closedExponent lastWidth (n + 1) = halfOpenExponent lastWidth n := by
  unfold closedExponent halfOpenExponent
  rw [show n + 1 + lastWidth - 1 = n + lastWidth by omega]
  simpa [one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.add_mul_div_right n 1 hwidth)

theorem closedExponent_eq_iff_interval_of_pos
    {lastWidth lastValue j : ℕ}
    (hwidth : 0 < lastWidth)
    (hj : 0 < j) :
    closedExponent lastWidth lastValue = j ↔
      (j - 1) * lastWidth < lastValue ∧ lastValue ≤ j * lastWidth := by
  cases lastValue with
  | zero =>
      constructor
      · intro h
        have hzero : closedExponent lastWidth 0 = 0 := by
          unfold closedExponent
          exact Nat.div_eq_of_lt (by
            simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt hwidth)))
        omega
      · intro h
        rcases h with ⟨hlower, hupper⟩
        have : ¬ (j - 1) * lastWidth < 0 := Nat.not_lt_zero _
        contradiction
  | succ n =>
      rw [closedExponent_succ_eq_halfOpenExponent hwidth]
      rw [halfOpenExponent_eq_iff_interval hwidth]
      constructor
      · intro h
        rcases h with ⟨hlower, hupper⟩
        constructor <;> omega
      · intro h
        rcases h with ⟨hlower, hupper⟩
        constructor <;> omega

theorem finalWidthOfWidths_pos_of_forall_pos
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    0 < finalWidthOfWidths startWidth restWidths := by
  induction restWidths generalizing startWidth with
  | nil =>
      simpa [finalWidthOfWidths] using hpos
  | cons width rest ih =>
      have hpos' : 0 < startWidth ∧ List.Forall (fun width => 0 < width) (width :: rest) := by
        simpa using hpos
      rcases hpos' with ⟨hstart, htail⟩
      simpa [finalWidthOfWidths] using (ih (startWidth := width) htail)

theorem ceilScaled_eq_zero_iff
    {prevWidth acc currWidth : ℕ}
    (hprev : 0 < prevWidth)
    (hcurr : 0 < currWidth) :
    ceilScaled prevWidth acc currWidth = 0 ↔ acc = 0 := by
  constructor
  · intro h
    by_cases hacc : acc = 0
    · exact hacc
    · have haccpos : 0 < acc := Nat.pos_of_ne_zero hacc
      have hbound : 1 * prevWidth ≤ currWidth * acc + prevWidth - 1 := by
        have : 1 ≤ currWidth * acc := Nat.succ_le_of_lt (Nat.mul_pos hcurr haccpos)
        omega
      have hquot : 1 ≤ ceilScaled prevWidth acc currWidth := by
        unfold ceilScaled
        exact (Nat.le_div_iff_mul_le hprev).2 hbound
      omega
  · intro hacc
    subst hacc
    unfold ceilScaled
    simpa [Nat.mul_zero] using (Nat.div_eq_of_lt (by
      simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt hprev))))

theorem mixedRadixStep_eq_zero_iff
    {prevWidth acc currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hcurr : 0 < currWidth) :
    mixedRadixStep prevWidth acc currWidth digit = 0 ↔ acc = 0 ∧ digit = 0 := by
  constructor
  · intro h
    have hdigit : digit = 0 := by
      unfold mixedRadixStep at h
      omega
    have hceil : ceilScaled prevWidth acc currWidth = 0 := by
      unfold mixedRadixStep at h
      omega
    exact ⟨(ceilScaled_eq_zero_iff hprev hcurr).1 hceil, hdigit⟩
  · intro h
    rcases h with ⟨hacc, hdigit⟩
    subst hacc
    subst hdigit
    have hceil0 : ceilScaled prevWidth 0 currWidth = 0 :=
      (ceilScaled_eq_zero_iff hprev hcurr).2 rfl
    simp [mixedRadixStep, hceil0]

theorem mixedRadixAux_eq_zero_iff
    {prevWidth acc : ℕ}
    {steps : List (ℕ × ℕ)}
    (hprev : 0 < prevWidth)
    (hpos : PositiveWidths steps) :
    mixedRadixAux prevWidth acc steps = 0 ↔
      acc = 0 ∧ List.Forall (fun step => step.2 = 0) steps := by
  induction steps generalizing prevWidth acc with
  | nil =>
      simp [mixedRadixAux]
  | cons step rest ih =>
      rcases step with ⟨currWidth, digit⟩
      rcases hpos with ⟨hcurr, hposRest⟩
      rw [mixedRadixAux]
      constructor
      · intro h
        rcases (ih hcurr hposRest).1 h with ⟨hstepzero, hrestzeros⟩
        rcases (mixedRadixStep_eq_zero_iff hprev hcurr).1 hstepzero with ⟨hacc, hdigit⟩
        exact ⟨hacc, by simpa [hdigit] using hrestzeros⟩
      · intro h
        rcases h with ⟨hacc, hzeros⟩
        have hzeros' : digit = 0 ∧ List.Forall (fun step => step.2 = 0) rest := by
          simpa using hzeros
        rcases hzeros' with ⟨hdigit, hrestzeros⟩
        have hstepzero : mixedRadixStep prevWidth acc currWidth digit = 0 :=
          (mixedRadixStep_eq_zero_iff hprev hcurr).2 ⟨hacc, hdigit⟩
        exact (ih hcurr hposRest).2 ⟨hstepzero, hrestzeros⟩

theorem digits_eq_replicate_zero_of_forall_zip_snd_eq_zero
    {widths digits : List ℕ}
    (hlen : widths.length = digits.length)
    (hzero : List.Forall (fun step => step.2 = 0) (widthDigitPairs widths digits)) :
    digits = List.replicate digits.length 0 := by
  induction widths generalizing digits with
  | nil =>
      cases digits <;> simp at hlen ⊢
  | cons width widths ih =>
      cases digits with
      | nil =>
          simp at hlen
      | cons digit digits =>
          have hzip : widthDigitPairs (width :: widths) (digit :: digits) =
              (width, digit) :: widthDigitPairs widths digits := by
            rfl
          rw [hzip] at hzero
          have hzero' :
              digit = 0 ∧ List.Forall (fun step => step.2 = 0) (widthDigitPairs widths digits) := by
            simpa using hzero
          rcases hzero' with ⟨hdigit, hrestzero⟩
          have htail : digits = List.replicate digits.length 0 :=
            ih (Nat.succ.inj hlen) hrestzero
          rw [hdigit, htail]
          simp [List.replicate_succ]

theorem forall_zero_widthDigitPairs_replicate
    {widths : List ℕ} :
    List.Forall (fun step => step.2 = 0)
      (widthDigitPairs widths (List.replicate widths.length 0)) := by
  induction widths with
  | nil =>
      simp [widthDigitPairs]
  | cons width widths ih =>
      simpa using (show List.Forall (fun step => step.2 = 0)
        (widthDigitPairs (width :: widths) (List.replicate (widths.length + 1) 0)) from by
          rw [List.replicate_succ]
          simpa [widthDigitPairs] using
            (show 0 = 0 ∧ List.Forall (fun step => step.2 = 0)
              (widthDigitPairs widths (List.replicate widths.length 0)) from ⟨rfl, ih⟩))

theorem replicate_zero_mem_digitBox_of_forall_pos
    {widths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) widths) :
    List.replicate widths.length 0 ∈ digitBox widths := by
  induction widths with
  | nil =>
      simp [digitBox]
  | cons width widths ih =>
      have hpos' : 0 < width ∧ List.Forall (fun width => 0 < width) widths := by
        simpa using hpos
      rcases hpos' with ⟨hwidth, hrest⟩
      simpa using (show List.replicate (widths.length + 1) 0 ∈ digitBox (width :: widths) from by
        rw [List.replicate_succ]
        simpa [digitBox, hwidth] using And.intro hwidth (ih hrest))

theorem closedExponent_eq_zero_iff
    {lastWidth lastValue : ℕ}
    (hwidth : 0 < lastWidth) :
    closedExponent lastWidth lastValue = 0 ↔ lastValue = 0 := by
  cases lastValue with
  | zero =>
      constructor
      · intro _
        rfl
      · intro _
        simpa [closedExponent, Nat.mul_zero] using (Nat.div_eq_of_lt (by
          simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt hwidth))))
  | succ n =>
      rw [closedExponent_succ_eq_halfOpenExponent hwidth]
      have hpos : 1 ≤ halfOpenExponent lastWidth n := halfOpenExponent_pos
      constructor <;> intro h <;> omega

theorem ceilScaled_mod_decomposition
    {prevWidth prevValue currWidth : ℕ}
    (hprev : 0 < prevWidth) :
    ceilScaled prevWidth prevValue currWidth =
      ceilScaled prevWidth (prevValue % prevWidth) currWidth +
        (prevValue / prevWidth) * currWidth := by
  unfold ceilScaled
  have hnum :
      currWidth * prevValue + prevWidth - 1 =
        currWidth * (prevValue % prevWidth) + prevWidth - 1 +
          ((prevValue / prevWidth) * currWidth) * prevWidth := by
    calc
      currWidth * prevValue + prevWidth - 1
          = currWidth * (prevValue % prevWidth + prevWidth * (prevValue / prevWidth)) +
              prevWidth - 1 := by
                nth_rewrite 1 [← Nat.mod_add_div prevValue prevWidth]
                rfl
      _ = currWidth * (prevValue % prevWidth) +
            currWidth * (prevWidth * (prevValue / prevWidth)) + prevWidth - 1 := by
              rw [Nat.mul_add]
      _ = currWidth * (prevValue % prevWidth) +
            (((prevValue / prevWidth) * currWidth) * prevWidth) + prevWidth - 1 := by
              simp [Nat.mul_left_comm, Nat.mul_comm]
      _ = currWidth * (prevValue % prevWidth) +
            ((((prevValue / prevWidth) * currWidth) * prevWidth) + (prevWidth - 1)) := by
              rw [Nat.add_sub_assoc (Nat.succ_le_of_lt hprev), Nat.add_assoc]
      _ = currWidth * (prevValue % prevWidth) + (prevWidth - 1) +
            (((prevValue / prevWidth) * currWidth) * prevWidth) := by
              simp [Nat.add_left_comm, Nat.add_comm]
      _ = currWidth * (prevValue % prevWidth) + prevWidth - 1 +
            (((prevValue / prevWidth) * currWidth) * prevWidth) := by
              omega
  rw [hnum, Nat.add_mul_div_right _ _ hprev]

theorem mixedRadixStep_eq_payload_add_quotient_part
    {prevWidth prevValue currWidth digit : ℕ}
    (hprev : 0 < prevWidth) :
    mixedRadixStep prevWidth prevValue currWidth digit =
      carryPayload prevWidth prevValue currWidth digit +
        (prevValue / prevWidth) * currWidth := by
  unfold mixedRadixStep carryPayload
  rw [ceilScaled_mod_decomposition hprev]
  simp [Nat.add_assoc]

theorem mixedRadixStep_div_eq_quotient_add_carry
    {prevWidth prevValue currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hcurr : 0 < currWidth) :
    mixedRadixStep prevWidth prevValue currWidth digit / currWidth =
      prevValue / prevWidth + carryIncrement prevWidth prevValue currWidth digit := by
  rw [mixedRadixStep_eq_payload_add_quotient_part hprev]
  rw [Nat.add_mul_div_right _ _ hcurr]
  simp [carryIncrement, add_comm]

theorem ceilScaled_le_of_lt
    {prevWidth rem currWidth : ℕ}
    (hprev : 0 < prevWidth)
    (hrem : rem < prevWidth)
    (hcurr : 0 < currWidth) :
    ceilScaled prevWidth rem currWidth ≤ currWidth := by
  unfold ceilScaled
  have hmul : currWidth * rem < currWidth * prevWidth :=
    Nat.mul_lt_mul_of_pos_left hrem hcurr
  have hpred : prevWidth - 1 < prevWidth := by
    simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt hprev))
  have hbound : currWidth * rem + prevWidth - 1 < (currWidth + 1) * prevWidth := by
    have hsum : currWidth * rem + (prevWidth - 1) < currWidth * prevWidth + prevWidth := by
      omega
    rw [Nat.add_sub_assoc (Nat.succ_le_of_lt hprev)]
    simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hprev).2 hbound)

theorem carryPayload_lt_two_mul_of_digit_lt
    {prevWidth prevValue currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hdigit : digit < currWidth) :
    carryPayload prevWidth prevValue currWidth digit < 2 * currWidth := by
  have hcurr : 0 < currWidth := lt_of_le_of_lt (Nat.zero_le digit) hdigit
  have hceil :
      ceilScaled prevWidth (prevValue % prevWidth) currWidth ≤ currWidth :=
    ceilScaled_le_of_lt hprev (Nat.mod_lt _ hprev) hcurr
  unfold carryPayload
  have hsum :
      digit + ceilScaled prevWidth (prevValue % prevWidth) currWidth <
        currWidth + currWidth := by
    exact Nat.add_lt_add_of_lt_of_le hdigit hceil
  simpa [two_mul] using hsum

theorem carryIncrement_lt_two_of_digit_lt
    {prevWidth prevValue currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hdigit : digit < currWidth) :
    carryIncrement prevWidth prevValue currWidth digit < 2 := by
  have hcurr : 0 < currWidth := lt_of_le_of_lt (Nat.zero_le digit) hdigit
  unfold carryIncrement
  rw [Nat.div_lt_iff_lt_mul hcurr]
  simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    carryPayload_lt_two_mul_of_digit_lt (prevValue := prevValue) hprev hdigit

theorem carryIncrement_le_one_of_digit_lt
    {prevWidth prevValue currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hdigit : digit < currWidth) :
    carryIncrement prevWidth prevValue currWidth digit ≤ 1 := by
  simpa using Nat.lt_succ_iff.mp (carryIncrement_lt_two_of_digit_lt hprev hdigit)

theorem carryIncrement_eq_zero_or_one_of_digit_lt
    {prevWidth prevValue currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hdigit : digit < currWidth) :
    carryIncrement prevWidth prevValue currWidth digit = 0 ∨
      carryIncrement prevWidth prevValue currWidth digit = 1 := by
  have hle : carryIncrement prevWidth prevValue currWidth digit ≤ 1 :=
    carryIncrement_le_one_of_digit_lt hprev hdigit
  omega

theorem dvd_finalWidth_of_chainDividesFrom
    {α : Type} {prevWidth : ℕ} {steps : List (ℕ × α)}
    (hchain : ChainDividesFrom prevWidth steps) :
    prevWidth ∣ finalWidth prevWidth steps := by
  induction steps generalizing prevWidth with
  | nil =>
      simp [finalWidth]
  | cons step rest ih =>
      rcases step with ⟨currWidth, payload⟩
      rcases hchain with ⟨hdiv, hrest⟩
      exact dvd_trans hdiv (ih hrest)

theorem quotient_mul_quotient_eq_quotient
    {a b c : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hab : a ∣ b)
    (hbc : b ∣ c) :
    (b / a) * (c / b) = c / a := by
  rcases hab with ⟨q, rfl⟩
  have hq : 0 < q := by
    by_cases hq0 : q = 0
    · simp [hq0] at hb
    · exact Nat.pos_of_ne_zero hq0
  rcases hbc with ⟨r, rfl⟩
  calc
    ((a * q) / a) * ((a * q * r) / (a * q))
        = q * ((a * q * r) / (a * q)) := by
            rw [Nat.mul_div_right _ ha]
    _ = q * r := by
          rw [show a * q * r = r * (a * q) by
                simp [Nat.mul_left_comm, Nat.mul_comm]]
          congr 1
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            (Nat.mul_div_right r hb)
    _ = ((q * r) * a) / a := by
          symm
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            (Nat.mul_div_right (q * r) ha)
    _ = (a * q * r) / a := by
          congr 1
          simp [Nat.mul_left_comm, Nat.mul_comm]

/--
If `prevWidth ∣ currWidth`, then the VW-CBS ceiling step collapses to the exact
linear scaling that appears in the divisor-chain specialization of the paper.
-/
theorem ceilScaled_eq_of_dvd
    {prevWidth acc currWidth : ℕ}
    (hprev : 0 < prevWidth)
    (hdiv : prevWidth ∣ currWidth) :
    ceilScaled prevWidth acc currWidth = (currWidth / prevWidth) * acc := by
  rcases hdiv with ⟨q, rfl⟩
  suffices hmain : ceilScaled prevWidth acc (prevWidth * q) = q * acc by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_div_right _ hprev] using hmain
  unfold ceilScaled
  have hlt : prevWidth - 1 < prevWidth := by
    simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt (Nat.ne_of_gt hprev))
  calc
    (prevWidth * q * acc + prevWidth - 1) / prevWidth
        = (prevWidth * (q * acc) + (prevWidth - 1)) / prevWidth := by
            rw [Nat.mul_assoc, Nat.add_sub_assoc (Nat.succ_le_of_lt hprev)]
    _ = ((prevWidth - 1) + (q * acc) * prevWidth) / prevWidth := by
          rw [Nat.add_comm, Nat.mul_comm prevWidth (q * acc)]
    _ = (prevWidth - 1) / prevWidth + q * acc := by
          rw [Nat.add_mul_div_right _ _ hprev]
    _ = q * acc := by
          rw [Nat.div_eq_of_lt hlt, zero_add]

/--
Under a divisor-chain step, the mixed-radix update is literally affine-linear.
-/
theorem mixedRadixStep_eq_of_dvd
    {prevWidth acc currWidth digit : ℕ}
    (hprev : 0 < prevWidth)
    (hdiv : prevWidth ∣ currWidth) :
    mixedRadixStep prevWidth acc currWidth digit =
      digit + (currWidth / prevWidth) * acc := by
  simp [mixedRadixStep, ceilScaled_eq_of_dvd hprev hdiv]

/--
Under divisor-chain hypotheses, the full recurrence has the expected weighted
sum closed form.
-/
theorem mixedRadixAux_eq_weightedDigitSum_of_chain
    {prevWidth acc : ℕ}
    {steps : List (ℕ × ℕ)}
    (hprev : 0 < prevWidth)
    (hchain : ChainDividesFrom prevWidth steps)
    (hpos : PositiveWidths steps) :
    mixedRadixAux prevWidth acc steps =
      acc * (finalWidth prevWidth steps / prevWidth) +
      weightedDigitSum (finalWidth prevWidth steps) steps := by
  induction steps generalizing prevWidth acc with
  | nil =>
      rw [mixedRadixAux, finalWidth, weightedDigitSum]
      rw [Nat.div_self hprev, Nat.mul_one, add_zero]
  | cons step rest ih =>
      rcases step with ⟨currWidth, digit⟩
      rcases hchain with ⟨hdiv, hchainRest⟩
      rcases hpos with ⟨hcurr, hposRest⟩
      have hfinalDiv : currWidth ∣ finalWidth currWidth rest :=
        dvd_finalWidth_of_chainDividesFrom hchainRest
      rw [mixedRadixAux, mixedRadixStep_eq_of_dvd hprev hdiv]
      rw [ih hcurr hchainRest hposRest]
      simp [finalWidth, weightedDigitSum, Nat.mul_add,
        Nat.mul_left_comm, Nat.mul_comm, add_left_comm, add_comm,
        quotient_mul_quotient_eq_quotient hprev hcurr hdiv hfinalDiv]

theorem mixedRadixAux_div_finalWidth_eq_quotient_plus_carryCount
    {prevWidth prevValue : ℕ}
    {steps : List (ℕ × ℕ)}
    (hprev : 0 < prevWidth)
    (hpos : PositiveWidths steps) :
    mixedRadixAux prevWidth prevValue steps / finalWidth prevWidth steps =
      prevValue / prevWidth + carryCountAux prevWidth prevValue steps := by
  induction steps generalizing prevWidth prevValue with
  | nil =>
      simp [mixedRadixAux, finalWidth, carryCountAux]
  | cons step rest ih =>
      rcases step with ⟨currWidth, digit⟩
      rcases hpos with ⟨hcurr, hposRest⟩
      rw [mixedRadixAux, finalWidth, carryCountAux]
      rw [ih hcurr hposRest, mixedRadixStep_div_eq_quotient_add_carry hprev hcurr]
      simp [add_assoc, add_left_comm, add_comm]

theorem mixedRadixFromPairs_eq_weightedDigitSum_of_chain
    {startWidth startDigit : ℕ}
    {steps : List (ℕ × ℕ)}
    (hstart : 0 < startWidth)
    (hchain : ChainDividesFrom startWidth steps)
    (hpos : PositiveWidths steps) :
    mixedRadixFromPairs ((startWidth, startDigit) :: steps) =
      weightedDigitSum (finalWidth startWidth steps) ((startWidth, startDigit) :: steps) := by
  simp [mixedRadixFromPairs, weightedDigitSum,
    mixedRadixAux_eq_weightedDigitSum_of_chain hstart hchain hpos]

theorem finalWidth_zip_eq_finalWidthOfWidths_of_length_eq
    {startWidth : ℕ}
    {widths digits : List ℕ}
    (hlen : widths.length = digits.length) :
    finalWidth startWidth (widthDigitPairs widths digits) =
      finalWidthOfWidths startWidth widths := by
  induction widths generalizing startWidth digits with
  | nil =>
      cases digits <;> simp [widthDigitPairs, finalWidth, finalWidthOfWidths] at hlen ⊢
  | cons width widths ih =>
      cases digits with
      | nil =>
          simp at hlen
      | cons digit digits =>
          simpa [widthDigitPairs, finalWidth, finalWidthOfWidths] using
            ih (Nat.succ.inj hlen)

theorem mixedRadixValue_div_eq_quotient_plus_carryCount
    {startWidth startDigit : ℕ}
    {restWidths restDigits : List ℕ}
    (hlen : restWidths.length = restDigits.length)
    (hstart : 0 < startWidth)
    (hpos : PositiveWidths (widthDigitPairs restWidths restDigits)) :
    mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits) /
        finalWidthOfWidths startWidth restWidths =
      startDigit / startWidth +
        carryCountValue (startWidth :: restWidths) (startDigit :: restDigits) := by
  rw [show finalWidthOfWidths startWidth restWidths =
      finalWidth startWidth (widthDigitPairs restWidths restDigits) by
        symm
        exact finalWidth_zip_eq_finalWidthOfWidths_of_length_eq hlen]
  simp [mixedRadixValue, carryCountValue, widthDigitPairs]
  simpa using
    (mixedRadixAux_div_finalWidth_eq_quotient_plus_carryCount
      (prevWidth := startWidth) (prevValue := startDigit)
      (steps := widthDigitPairs restWidths restDigits) hstart hpos)

theorem mixedRadixValue_div_eq_carryCount_of_head_lt
    {startWidth startDigit : ℕ}
    {restWidths restDigits : List ℕ}
    (hlen : restWidths.length = restDigits.length)
    (hstart : 0 < startWidth)
    (hhead : startDigit < startWidth)
    (hpos : PositiveWidths (widthDigitPairs restWidths restDigits)) :
    mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits) /
        finalWidthOfWidths startWidth restWidths =
      carryCountValue (startWidth :: restWidths) (startDigit :: restDigits) := by
  rw [mixedRadixValue_div_eq_quotient_plus_carryCount hlen hstart hpos,
    Nat.div_eq_of_lt hhead, zero_add]

theorem mixedRadixValue_div_eq_carryCount_of_mem_digitBox
    {startWidth startDigit : ℕ}
    {restWidths restDigits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : startDigit :: restDigits ∈ digitBox (startWidth :: restWidths)) :
    mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits) /
        finalWidthOfWidths startWidth restWidths =
      carryCountValue (startWidth :: restWidths) (startDigit :: restDigits) := by
  have hheadTail : startDigit < startWidth ∧ restDigits ∈ digitBox restWidths := by
    simpa [digitBox] using hmem
  rcases hheadTail with ⟨hhead, htailmem⟩
  have hpos' : 0 < startWidth ∧ List.Forall (fun width => 0 < width) restWidths := by
    simpa using hpos
  rcases hpos' with ⟨hstart, hposRest⟩
  have hlen : restWidths.length = restDigits.length := by
    simpa using (mem_digitBox_length htailmem).symm
  have hpairpos : PositiveWidths (widthDigitPairs restWidths restDigits) :=
    positiveWidths_widthDigitPairs_of_forall_pos hposRest
  exact mixedRadixValue_div_eq_carryCount_of_head_lt hlen hstart hhead hpairpos

theorem halfOpenExponent_eq_one_add_carryCountValue_of_head_lt
    {startWidth startDigit : ℕ}
    {restWidths restDigits : List ℕ}
    (hlen : restWidths.length = restDigits.length)
    (hstart : 0 < startWidth)
    (hhead : startDigit < startWidth)
    (hpos : PositiveWidths (widthDigitPairs restWidths restDigits)) :
    halfOpenExponent
        (finalWidthOfWidths startWidth restWidths)
        (mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits)) =
      1 + carryCountValue (startWidth :: restWidths) (startDigit :: restDigits) := by
  unfold halfOpenExponent
  rw [mixedRadixValue_div_eq_carryCount_of_head_lt hlen hstart hhead hpos]
  simp [add_comm]

theorem halfOpenExponent_eq_one_add_carryCountValue_of_mem_digitBox
    {startWidth startDigit : ℕ}
    {restWidths restDigits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : startDigit :: restDigits ∈ digitBox (startWidth :: restWidths)) :
    halfOpenExponent
        (finalWidthOfWidths startWidth restWidths)
        (mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits)) =
      1 + carryCountValue (startWidth :: restWidths) (startDigit :: restDigits) := by
  unfold halfOpenExponent
  rw [mixedRadixValue_div_eq_carryCount_of_mem_digitBox hpos hmem]
  simp [add_comm]

theorem digitBoxHalfOpenExponent_eq_one_add_digitBoxCarryCount_of_mem
    {startWidth : ℕ}
    {restWidths digits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : digits ∈ digitBox (startWidth :: restWidths)) :
    digitBoxHalfOpenExponent startWidth restWidths digits =
      1 + digitBoxCarryCount startWidth restWidths digits := by
  cases digits with
  | nil =>
      simp [digitBox] at hmem
  | cons startDigit restDigits =>
      simpa [digitBoxHalfOpenExponent, digitBoxCarryCount] using
        (halfOpenExponent_eq_one_add_carryCountValue_of_mem_digitBox
          (startWidth := startWidth) (startDigit := startDigit)
          (restWidths := restWidths) (restDigits := restDigits) hpos hmem)

theorem digitBoxClosedExponent_eq_iff_interval_of_mem_of_pos
    {startWidth : ℕ}
    {restWidths digits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : digits ∈ digitBox (startWidth :: restWidths))
    {j : ℕ}
    (hj : 0 < j) :
    digitBoxClosedExponent startWidth restWidths digits = j ↔
      (j - 1) * finalWidthOfWidths startWidth restWidths <
          digitBoxLastValue startWidth restWidths digits ∧
        digitBoxLastValue startWidth restWidths digits ≤
          j * finalWidthOfWidths startWidth restWidths := by
  have hfinal : 0 < finalWidthOfWidths startWidth restWidths :=
    finalWidthOfWidths_pos_of_forall_pos hpos
  cases digits with
  | nil =>
      simp [digitBox] at hmem
  | cons startDigit restDigits =>
      simpa [digitBoxClosedExponent, digitBoxLastValue, mixedRadixValue] using
        (closedExponent_eq_iff_interval_of_pos
          (lastWidth := finalWidthOfWidths startWidth restWidths)
          (lastValue := digitBoxLastValue startWidth restWidths (startDigit :: restDigits))
          (j := j) hfinal hj)

theorem digitBoxHalfOpenExponent_eq_iff_interval_of_mem
    {startWidth : ℕ}
    {restWidths digits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : digits ∈ digitBox (startWidth :: restWidths))
    (j : ℕ) :
    digitBoxHalfOpenExponent startWidth restWidths digits = j ↔
      (j - 1) * finalWidthOfWidths startWidth restWidths ≤
          digitBoxLastValue startWidth restWidths digits ∧
        digitBoxLastValue startWidth restWidths digits <
          j * finalWidthOfWidths startWidth restWidths := by
  have hfinal : 0 < finalWidthOfWidths startWidth restWidths :=
    finalWidthOfWidths_pos_of_forall_pos hpos
  cases digits with
  | nil =>
      simp [digitBox] at hmem
  | cons startDigit restDigits =>
      simpa [digitBoxHalfOpenExponent, digitBoxLastValue, mixedRadixValue] using
        (halfOpenExponent_eq_iff_interval
          (lastWidth := finalWidthOfWidths startWidth restWidths)
          (lastValue := mixedRadixValue (startWidth :: restWidths) (startDigit :: restDigits))
          (j := j) hfinal)

theorem etaCoeff_eq_card_filter_carryCount
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (j : ℕ) :
    etaCoeff startWidth restWidths j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        1 + digitBoxCarryCount startWidth restWidths digits = j).card := by
  have hfilter :
      (digitBox (startWidth :: restWidths)).filter (fun digits =>
          digitBoxHalfOpenExponent startWidth restWidths digits = j) =
        (digitBox (startWidth :: restWidths)).filter (fun digits =>
          1 + digitBoxCarryCount startWidth restWidths digits = j) := by
    ext digits
    simp only [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨hmem, hexp⟩
      constructor
      · exact hmem
      · rw [digitBoxHalfOpenExponent_eq_one_add_digitBoxCarryCount_of_mem hpos hmem] at hexp
        exact hexp
    · intro h
      rcases h with ⟨hmem, hcarry⟩
      constructor
      · exact hmem
      · rw [digitBoxHalfOpenExponent_eq_one_add_digitBoxCarryCount_of_mem hpos hmem]
        exact hcarry
  simpa [etaCoeff] using congrArg Finset.card hfilter

theorem hStarCoeff_eq_card_filter_interval_of_pos
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    {j : ℕ}
    (hj : 0 < j) :
    hStarCoeff startWidth restWidths j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        (j - 1) * finalWidthOfWidths startWidth restWidths <
            digitBoxLastValue startWidth restWidths digits ∧
          digitBoxLastValue startWidth restWidths digits ≤
            j * finalWidthOfWidths startWidth restWidths).card := by
  have hfilter :
      (digitBox (startWidth :: restWidths)).filter (fun digits =>
          digitBoxClosedExponent startWidth restWidths digits = j) =
        (digitBox (startWidth :: restWidths)).filter (fun digits =>
          (j - 1) * finalWidthOfWidths startWidth restWidths <
              digitBoxLastValue startWidth restWidths digits ∧
            digitBoxLastValue startWidth restWidths digits ≤
              j * finalWidthOfWidths startWidth restWidths) := by
    ext digits
    simp only [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨hmem, hclosed⟩
      constructor
      · exact hmem
      · exact (digitBoxClosedExponent_eq_iff_interval_of_mem_of_pos hpos hmem hj).1 hclosed
    · intro h
      rcases h with ⟨hmem, hinterval⟩
      constructor
      · exact hmem
      · exact (digitBoxClosedExponent_eq_iff_interval_of_mem_of_pos hpos hmem hj).2 hinterval
  simpa [hStarCoeff] using congrArg Finset.card hfilter

theorem digitBoxLastValue_eq_zero_iff_eq_replicate_zero_of_mem
    {startWidth : ℕ}
    {restWidths digits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : digits ∈ digitBox (startWidth :: restWidths)) :
    digitBoxLastValue startWidth restWidths digits = 0 ↔
      digits = List.replicate digits.length 0 := by
  cases digits with
  | nil =>
      simp [digitBox] at hmem
  | cons startDigit restDigits =>
      have hheadTail : startDigit < startWidth ∧ restDigits ∈ digitBox restWidths := by
        simpa [digitBox] using hmem
      rcases hheadTail with ⟨hhead, htailmem⟩
      have hpos' : 0 < startWidth ∧ List.Forall (fun width => 0 < width) restWidths := by
        simpa using hpos
      rcases hpos' with ⟨hstart, hposRest⟩
      have hlen : restWidths.length = restDigits.length := by
        simpa using (mem_digitBox_length htailmem).symm
      have hpairpos : PositiveWidths (widthDigitPairs restWidths restDigits) :=
        positiveWidths_widthDigitPairs_of_forall_pos hposRest
      constructor
      · intro hzero
        have hauxzero :
            mixedRadixAux startWidth startDigit (widthDigitPairs restWidths restDigits) = 0 := by
          dsimp [digitBoxLastValue] at hzero
          dsimp [mixedRadixValue] at hzero
          exact hzero
        rcases (mixedRadixAux_eq_zero_iff hstart hpairpos).1 hauxzero with
          ⟨hstartzero, hrestzero⟩
        have hrestdigits : restDigits = List.replicate restDigits.length 0 :=
          digits_eq_replicate_zero_of_forall_zip_snd_eq_zero hlen hrestzero
        rw [hstartzero, hrestdigits]
        simp [List.replicate_succ]
      · intro hdigits
        have hdigits' : startDigit :: restDigits = 0 :: List.replicate restDigits.length 0 := by
          simpa [List.replicate_succ] using hdigits
        injection hdigits' with hstartzero hrestdigits
        rw [hstartzero, hrestdigits]
        have hpairposZero :
            PositiveWidths (widthDigitPairs restWidths (List.replicate restWidths.length 0)) :=
          positiveWidths_widthDigitPairs_of_forall_pos hposRest
        have hauxzero :
            mixedRadixAux startWidth 0
                (widthDigitPairs restWidths (List.replicate restDigits.length 0)) = 0 := by
          simpa [hlen] using
            ((mixedRadixAux_eq_zero_iff hstart hpairposZero).2
              ⟨rfl, forall_zero_widthDigitPairs_replicate⟩)
        simpa [digitBoxLastValue, mixedRadixValue] using hauxzero

theorem digitBoxClosedExponent_eq_zero_iff_eq_replicate_zero_of_mem
    {startWidth : ℕ}
    {restWidths digits : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (hmem : digits ∈ digitBox (startWidth :: restWidths)) :
    digitBoxClosedExponent startWidth restWidths digits = 0 ↔
      digits = List.replicate digits.length 0 := by
  have hfinal : 0 < finalWidthOfWidths startWidth restWidths :=
    finalWidthOfWidths_pos_of_forall_pos hpos
  cases digits with
  | nil =>
      simp [digitBox] at hmem
  | cons startDigit restDigits =>
      rw [show digitBoxClosedExponent startWidth restWidths (startDigit :: restDigits) = 0 ↔
          digitBoxLastValue startWidth restWidths (startDigit :: restDigits) = 0 by
            simpa [digitBoxClosedExponent, digitBoxLastValue] using
              (closedExponent_eq_zero_iff
                (lastWidth := finalWidthOfWidths startWidth restWidths)
                (lastValue := digitBoxLastValue startWidth restWidths (startDigit :: restDigits))
                hfinal)]
      exact digitBoxLastValue_eq_zero_iff_eq_replicate_zero_of_mem hpos hmem

theorem hStarCoeff_zero_eq_one
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    hStarCoeff startWidth restWidths 0 = 1 := by
  let zeroDigits := List.replicate (List.length (startWidth :: restWidths)) 0
  have hzeroMem : zeroDigits ∈ digitBox (startWidth :: restWidths) :=
    replicate_zero_mem_digitBox_of_forall_pos hpos
  have hfilter :
      (digitBox (startWidth :: restWidths)).filter (fun digits =>
          digitBoxClosedExponent startWidth restWidths digits = 0) = {zeroDigits} := by
    ext digits
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with ⟨hmem, hzero⟩
      have hdigits : digits = List.replicate digits.length 0 :=
        (digitBoxClosedExponent_eq_zero_iff_eq_replicate_zero_of_mem hpos hmem).1 hzero
      have hlenDigits : digits.length = List.length (startWidth :: restWidths) :=
        mem_digitBox_length hmem
      calc
        digits = List.replicate digits.length 0 := hdigits
        _ = zeroDigits := by simp [zeroDigits, hlenDigits]
    · intro hdigits
      subst digits
      constructor
      · exact hzeroMem
      · exact
          (digitBoxClosedExponent_eq_zero_iff_eq_replicate_zero_of_mem hpos hzeroMem).2
            (by simp [zeroDigits])
  simpa [hStarCoeff] using congrArg Finset.card hfilter

theorem etaCoeff_eq_card_filter_interval
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (j : ℕ) :
    etaCoeff startWidth restWidths j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        (j - 1) * finalWidthOfWidths startWidth restWidths ≤
            digitBoxLastValue startWidth restWidths digits ∧
          digitBoxLastValue startWidth restWidths digits <
            j * finalWidthOfWidths startWidth restWidths).card := by
  have hfilter :
      (digitBox (startWidth :: restWidths)).filter (fun digits =>
          digitBoxHalfOpenExponent startWidth restWidths digits = j) =
        (digitBox (startWidth :: restWidths)).filter (fun digits =>
          (j - 1) * finalWidthOfWidths startWidth restWidths ≤
              digitBoxLastValue startWidth restWidths digits ∧
            digitBoxLastValue startWidth restWidths digits <
              j * finalWidthOfWidths startWidth restWidths) := by
    ext digits
    simp only [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨hmem, hexp⟩
      constructor
      · exact hmem
      · exact (digitBoxHalfOpenExponent_eq_iff_interval_of_mem hpos hmem j).1 hexp
    · intro h
      rcases h with ⟨hmem, hinterval⟩
      constructor
      · exact hmem
      · exact (digitBoxHalfOpenExponent_eq_iff_interval_of_mem hpos hmem j).2 hinterval
  simpa [etaCoeff] using congrArg Finset.card hfilter

theorem numeratorCoeff_closed_zero_eq_one
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    numeratorCoeff NumeratorKind.closed startWidth restWidths 0 = 1 := by
  simpa using hStarCoeff_zero_eq_one hpos

theorem numeratorCoeff_closed_eq_card_filter_interval_of_pos
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    {j : ℕ}
    (hj : 0 < j) :
    numeratorCoeff NumeratorKind.closed startWidth restWidths j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        (j - 1) * finalWidthOfWidths startWidth restWidths <
            digitBoxLastValue startWidth restWidths digits ∧
          digitBoxLastValue startWidth restWidths digits ≤
            j * finalWidthOfWidths startWidth restWidths).card := by
  simpa using hStarCoeff_eq_card_filter_interval_of_pos hpos hj

theorem numeratorCoeff_halfOpen_eq_card_filter_carryCount
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (j : ℕ) :
    numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        1 + digitBoxCarryCount startWidth restWidths digits = j).card := by
  simpa using etaCoeff_eq_card_filter_carryCount hpos j

theorem numeratorCoeff_halfOpen_eq_card_filter_interval
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (j : ℕ) :
    numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        (j - 1) * finalWidthOfWidths startWidth restWidths ≤
            digitBoxLastValue startWidth restWidths digits ∧
          digitBoxLastValue startWidth restWidths digits <
            j * finalWidthOfWidths startWidth restWidths).card := by
  simpa using etaCoeff_eq_card_filter_interval hpos j

theorem numeratorCoeff_closed_bundle
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    numeratorCoeff NumeratorKind.closed startWidth restWidths 0 = 1 ∧
      ∀ j, 0 < j →
        numeratorCoeff NumeratorKind.closed startWidth restWidths j =
          ((digitBox (startWidth :: restWidths)).filter fun digits =>
            (j - 1) * finalWidthOfWidths startWidth restWidths <
                digitBoxLastValue startWidth restWidths digits ∧
              digitBoxLastValue startWidth restWidths digits ≤
                j * finalWidthOfWidths startWidth restWidths).card := by
  constructor
  · exact numeratorCoeff_closed_zero_eq_one hpos
  · intro j hj
    exact numeratorCoeff_closed_eq_card_filter_interval_of_pos hpos hj

theorem numeratorCoeff_halfOpen_bundle
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    (∀ j, numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
        ((digitBox (startWidth :: restWidths)).filter fun digits =>
          1 + digitBoxCarryCount startWidth restWidths digits = j).card) ∧
      ∀ j, numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
        ((digitBox (startWidth :: restWidths)).filter fun digits =>
          (j - 1) * finalWidthOfWidths startWidth restWidths ≤
              digitBoxLastValue startWidth restWidths digits ∧
            digitBoxLastValue startWidth restWidths digits <
              j * finalWidthOfWidths startWidth restWidths).card := by
  constructor
  · intro j
    exact numeratorCoeff_halfOpen_eq_card_filter_carryCount hpos j
  · intro j
    exact numeratorCoeff_halfOpen_eq_card_filter_interval hpos j

theorem numeratorCoeff_manuscript_bundle
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    numeratorCoeff NumeratorKind.closed startWidth restWidths 0 = 1 ∧
      (∀ j, 0 < j →
        numeratorCoeff NumeratorKind.closed startWidth restWidths j =
          ((digitBox (startWidth :: restWidths)).filter fun digits =>
            (j - 1) * finalWidthOfWidths startWidth restWidths <
                digitBoxLastValue startWidth restWidths digits ∧
              digitBoxLastValue startWidth restWidths digits ≤
                j * finalWidthOfWidths startWidth restWidths).card) ∧
      (∀ j, numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
        ((digitBox (startWidth :: restWidths)).filter fun digits =>
          1 + digitBoxCarryCount startWidth restWidths digits = j).card) ∧
      ∀ j, numeratorCoeff NumeratorKind.halfOpen startWidth restWidths j =
        ((digitBox (startWidth :: restWidths)).filter fun digits =>
          (j - 1) * finalWidthOfWidths startWidth restWidths ≤
              digitBoxLastValue startWidth restWidths digits ∧
            digitBoxLastValue startWidth restWidths digits <
              j * finalWidthOfWidths startWidth restWidths).card := by
  rcases numeratorCoeff_closed_bundle hpos with ⟨hzero, hclosed⟩
  rcases numeratorCoeff_halfOpen_bundle hpos with ⟨hcarry, hinterval⟩
  exact ⟨hzero, hclosed, hcarry, hinterval⟩

theorem coeff_hStarPolynomial_zero_eq_one
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    Polynomial.coeff (hStarPolynomial startWidth restWidths) 0 = 1 := by
  simpa using hStarCoeff_zero_eq_one hpos

theorem coeff_hStarPolynomial_eq_card_filter_interval_of_pos
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    {j : ℕ}
    (hj : 0 < j) :
    Polynomial.coeff (hStarPolynomial startWidth restWidths) j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        (j - 1) * finalWidthOfWidths startWidth restWidths <
            digitBoxLastValue startWidth restWidths digits ∧
          digitBoxLastValue startWidth restWidths digits ≤
            j * finalWidthOfWidths startWidth restWidths).card := by
  simpa using hStarCoeff_eq_card_filter_interval_of_pos hpos hj

theorem coeff_etaPolynomial_eq_card_filter_carryCount
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (j : ℕ) :
    Polynomial.coeff (etaPolynomial startWidth restWidths) j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        1 + digitBoxCarryCount startWidth restWidths digits = j).card := by
  simpa using etaCoeff_eq_card_filter_carryCount hpos j

theorem coeff_etaPolynomial_eq_card_filter_interval
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths))
    (j : ℕ) :
    Polynomial.coeff (etaPolynomial startWidth restWidths) j =
      ((digitBox (startWidth :: restWidths)).filter fun digits =>
        (j - 1) * finalWidthOfWidths startWidth restWidths ≤
            digitBoxLastValue startWidth restWidths digits ∧
          digitBoxLastValue startWidth restWidths digits <
            j * finalWidthOfWidths startWidth restWidths).card := by
  simpa using etaCoeff_eq_card_filter_interval hpos j

theorem numeratorPolynomial_bundle
    {startWidth : ℕ}
    {restWidths : List ℕ}
    (hpos : List.Forall (fun width => 0 < width) (startWidth :: restWidths)) :
    Polynomial.coeff (hStarPolynomial startWidth restWidths) 0 = 1 ∧
      (∀ j, 0 < j →
        Polynomial.coeff (hStarPolynomial startWidth restWidths) j =
          ((digitBox (startWidth :: restWidths)).filter fun digits =>
            (j - 1) * finalWidthOfWidths startWidth restWidths <
                digitBoxLastValue startWidth restWidths digits ∧
              digitBoxLastValue startWidth restWidths digits ≤
                j * finalWidthOfWidths startWidth restWidths).card) ∧
      (∀ j, Polynomial.coeff (etaPolynomial startWidth restWidths) j =
        ((digitBox (startWidth :: restWidths)).filter fun digits =>
          1 + digitBoxCarryCount startWidth restWidths digits = j).card) ∧
      ∀ j, Polynomial.coeff (etaPolynomial startWidth restWidths) j =
        ((digitBox (startWidth :: restWidths)).filter fun digits =>
          (j - 1) * finalWidthOfWidths startWidth restWidths ≤
              digitBoxLastValue startWidth restWidths digits ∧
            digitBoxLastValue startWidth restWidths digits <
              j * finalWidthOfWidths startWidth restWidths).card := by
  refine ⟨coeff_hStarPolynomial_zero_eq_one hpos, ?_, ?_, ?_⟩
  · intro j hj
    exact coeff_hStarPolynomial_eq_card_filter_interval_of_pos hpos hj
  · intro j
    exact coeff_etaPolynomial_eq_card_filter_carryCount hpos j
  · intro j
    exact coeff_etaPolynomial_eq_card_filter_interval hpos j

end CbsLean
