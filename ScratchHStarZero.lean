import CbsLean.VWNumerator

namespace CbsLean

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
          have hzero' : digit = 0 ∧ List.Forall (fun step => step.2 = 0) (widthDigitPairs widths digits) := by
            simpa using hzero
          rcases hzero' with ⟨hdigit, hrestzero⟩
          have htail : digits = List.replicate digits.length 0 :=
            ih (Nat.succ.inj hlen) hrestzero
          rw [hdigit, htail]
          simpa [List.replicate_succ]

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
        have hauxzero : mixedRadixAux startWidth startDigit (widthDigitPairs restWidths restDigits) = 0 := by
          dsimp [digitBoxLastValue] at hzero
          dsimp [mixedRadixValue] at hzero
          exact hzero
        rcases (mixedRadixAux_eq_zero_iff hstart hpairpos).1 hauxzero with ⟨hstartzero, hrestzero⟩
        have hrestdigits : restDigits = List.replicate restDigits.length 0 :=
          digits_eq_replicate_zero_of_forall_zip_snd_eq_zero hlen hrestzero
        rw [hstartzero, hrestdigits]
        simpa [List.replicate_succ]
      · intro hdigits
        have hdigits' : startDigit :: restDigits = 0 :: List.replicate restDigits.length 0 := by
          simpa [List.replicate_succ] using hdigits
        injection hdigits' with hstartzero hrestdigits
        rw [hstartzero, hrestdigits]
        have hpairposZero : PositiveWidths (widthDigitPairs restWidths (List.replicate restWidths.length 0)) :=
          positiveWidths_widthDigitPairs_of_forall_pos hposRest
        have hauxzero : mixedRadixAux startWidth 0 (widthDigitPairs restWidths (List.replicate restDigits.length 0)) = 0 := by
          simpa [hlen] using ((mixedRadixAux_eq_zero_iff hstart hpairposZero).2 ⟨rfl, forall_zero_widthDigitPairs_replicate⟩)
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
                (lastValue := digitBoxLastValue startWidth restWidths (startDigit :: restDigits)) hfinal)]
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
      · exact (digitBoxClosedExponent_eq_zero_iff_eq_replicate_zero_of_mem hpos hzeroMem).2 (by simp [zeroDigits])
  simpa [hStarCoeff] using congrArg Finset.card hfilter

end CbsLean
