import CbsLean.MagicCapacityCharacterizationGeneral

namespace CbsLean
namespace MagicCapacity

/-!
# Local magic residues

The global exact-insertion classification asks for zero insertion defect at every
source index.  This module isolates the weaker local object needed by the next
stage of the magic-capacity program: the residue classes at which a fixed
width triple is exact even when the triple is not globally exact.
-/

/-- Exact insertion at one source index. -/
def IsLocalMagic
    (sourceWidth middleWidth targetWidth x : ℕ) : Prop :=
  insertionDefect sourceWidth middleWidth targetWidth x = 0

/--
Local exactness is equivalent to one capacity inequality.  The direct lift is
always no larger than the lift through the inserted middle width, so equality
holds exactly when the inserted lift also fits under the direct target index.
-/
theorem isLocalMagic_iff_capacityInequality
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    IsLocalMagic sourceWidth middleWidth targetWidth x ↔
      targetWidth * indexLift sourceWidth middleWidth x ≤
        middleWidth * indexLift sourceWidth targetWidth x := by
  unfold IsLocalMagic
  rw [insertionDefect_eq_zero_iff hsource hmiddle]
  constructor
  · intro heq
    have hle :
        insertionComposite sourceWidth middleWidth targetWidth x ≤
          indexLift sourceWidth targetWidth x := by
      simpa [heq]
    simpa [insertionComposite] using
      ((indexLift_le_iff
        (sourceWidth := middleWidth)
        (targetWidth := targetWidth)
        (x := indexLift sourceWidth middleWidth x)
        (y := indexLift sourceWidth targetWidth x)
        hmiddle).1 hle)
  · intro hcapacity
    apply Nat.le_antisymm
    · exact
        (indexLift_le_iff
          (sourceWidth := middleWidth)
          (targetWidth := targetWidth)
          (x := indexLift sourceWidth middleWidth x)
          (y := indexLift sourceWidth targetWidth x)
          hmiddle).2 hcapacity
    · exact indexLift_le_insertionComposite hsource hmiddle

/-- The local-magic predicate is periodic modulo the source width. -/
theorem isLocalMagic_add_sourceWidth_iff
    {sourceWidth middleWidth targetWidth x : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    IsLocalMagic sourceWidth middleWidth targetWidth (x + sourceWidth) ↔
      IsLocalMagic sourceWidth middleWidth targetWidth x := by
  unfold IsLocalMagic
  rw [insertionDefect_add_sourceWidth hsource hmiddle]

/-- The canonical finite residue set representing all locally exact indices. -/
def localMagicResidues
    (sourceWidth middleWidth targetWidth : ℕ) : Finset ℕ :=
  (Finset.range sourceWidth).filter fun x =>
    IsLocalMagic sourceWidth middleWidth targetWidth x

@[simp] theorem mem_localMagicResidues
    {sourceWidth middleWidth targetWidth x : ℕ} :
    x ∈ localMagicResidues sourceWidth middleWidth targetWidth ↔
      x < sourceWidth ∧
        IsLocalMagic sourceWidth middleWidth targetWidth x := by
  simp [localMagicResidues]

/-- Every globally exact triple has every source residue locally magic. -/
theorem localMagicResidues_eq_range_of_globallyExact
    {sourceWidth middleWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (hexact : GloballyExactInsertion sourceWidth middleWidth targetWidth) :
    localMagicResidues sourceWidth middleWidth targetWidth =
      Finset.range sourceWidth := by
  apply Finset.ext
  intro x
  simp only [mem_localMagicResidues, Finset.mem_range]
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    unfold IsLocalMagic
    apply (insertionDefect_eq_zero_iff hsource hmiddle).2
    exact hexact x

end MagicCapacity
end CbsLean
