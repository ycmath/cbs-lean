import CbsLean.VWNumerator

namespace CbsLean

example {widths : List ℕ} :
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

example {widths : List ℕ}
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

end CbsLean
