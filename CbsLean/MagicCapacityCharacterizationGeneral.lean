import CbsLean.MagicCapacityCharacterization
import Mathlib.Data.Nat.GCD.Basic

namespace CbsLean
namespace MagicCapacity

/-!
# General exact-insertion characterization

This exploratory module removes the coprimality restriction.  It first proves
that global exactness forces the endpoint gcd to divide the inserted width,
then cancels the common factor and applies the coprime characterization.
-/

/-- Common positive scaling of both widths does not change an index lift. -/
theorem indexLift_mul_common
    {common sourceWidth targetWidth x : ℕ}
    (hcommon : 0 < common)
    (hsource : 0 < sourceWidth) :
    indexLift (common * sourceWidth) (common * targetWidth) x =
      indexLift sourceWidth targetWidth x := by
  apply Nat.le_antisymm
  · apply (indexLift_le_iff (Nat.mul_pos hcommon hsource)).2
    have hspec :
        targetWidth * x ≤
          sourceWidth * indexLift sourceWidth targetWidth x :=
      indexLift_spec
        (sourceWidth := sourceWidth)
        (targetWidth := targetWidth)
        (x := x) hsource
    calc
      (common * targetWidth) * x = common * (targetWidth * x) := by ring
      _ ≤ common *
          (sourceWidth * indexLift sourceWidth targetWidth x) :=
        Nat.mul_le_mul_left common hspec
      _ = (common * sourceWidth) *
          indexLift sourceWidth targetWidth x := by ring
  · apply (indexLift_le_iff hsource).2
    have hscaled :
        (common * targetWidth) * x ≤
          (common * sourceWidth) *
            indexLift (common * sourceWidth) (common * targetWidth) x :=
      indexLift_spec
        (sourceWidth := common * sourceWidth)
        (targetWidth := common * targetWidth)
        (x := x) (Nat.mul_pos hcommon hsource)
    have hnormalized :
        common * (targetWidth * x) ≤
          common *
            (sourceWidth *
              indexLift (common * sourceWidth) (common * targetWidth) x) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled
    exact Nat.le_of_mul_le_mul_left hnormalized hcommon

/-- Common scaling also cancels through an inserted middle width. -/
theorem insertionComposite_mul_common
    {common sourceWidth middleWidth targetWidth x : ℕ}
    (hcommon : 0 < common)
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth) :
    insertionComposite
        (common * sourceWidth)
        (common * middleWidth)
        (common * targetWidth)
        x =
      insertionComposite sourceWidth middleWidth targetWidth x := by
  unfold insertionComposite
  rw [indexLift_mul_common hcommon hsource]
  rw [indexLift_mul_common hcommon hmiddle]

/-- The endpoint gcd is positive when the source width is positive. -/
theorem endpointGcd_pos
    {sourceWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth) :
    0 < Nat.gcd sourceWidth targetWidth :=
  Nat.gcd_pos_of_pos_left targetWidth hsource

/--
Global exactness forces the endpoint gcd to divide the inserted middle width.
The witness index is `sourceWidth / gcd(sourceWidth,targetWidth)`.
-/
theorem endpointGcd_dvd_middle_of_globallyExactInsertion
    {sourceWidth middleWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (htarget : 0 < targetWidth)
    (hexact : GloballyExactInsertion
      sourceWidth middleWidth targetWidth) :
    Nat.gcd sourceWidth targetWidth ∣ middleWidth := by
  let d := Nat.gcd sourceWidth targetWidth
  let p := sourceWidth / d
  let q := targetWidth / d
  have hdpos : 0 < d := by
    simpa [d] using endpointGcd_pos (targetWidth := targetWidth) hsource
  have hdp : d ∣ sourceWidth := by
    simpa [d] using Nat.gcd_dvd_left sourceWidth targetWidth
  have hdq : d ∣ targetWidth := by
    simpa [d] using Nat.gcd_dvd_right sourceWidth targetWidth
  have hpFactor : sourceWidth = d * p := by
    calc
      sourceWidth = (sourceWidth / d) * d :=
        (Nat.div_mul_cancel hdp).symm
      _ = d * p := by simp [p, Nat.mul_comm]
  have hqFactor : targetWidth = d * q := by
    calc
      targetWidth = (targetWidth / d) * d :=
        (Nat.div_mul_cancel hdq).symm
      _ = d * q := by simp [q, Nat.mul_comm]
  have hp : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hpzero
    rw [hpzero, Nat.mul_zero] at hpFactor
    omega
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hqzero
    rw [hqzero, Nat.mul_zero] at hqFactor
    omega
  have hcross : targetWidth * p = sourceWidth * q := by
    rw [hpFactor, hqFactor]
    ring
  have hdirect : indexLift sourceWidth targetWidth p = q :=
    indexLift_eq_of_mul_add_eq hsource hsource (by simpa using hcross)
  let y := indexLift sourceWidth middleWidth p
  have hinner : middleWidth * p ≤ sourceWidth * y := by
    simpa [y] using
      (indexLift_spec
        (sourceWidth := sourceWidth)
        (targetWidth := middleWidth)
        (x := p) hsource)
  have houterEq : indexLift middleWidth targetWidth y = q := by
    have h := hexact p
    rw [insertionComposite, hdirect] at h
    simpa [y] using h
  have houter : targetWidth * y ≤ middleWidth * q := by
    have hspec :=
      indexLift_spec
        (sourceWidth := middleWidth)
        (targetWidth := targetWidth)
        (x := y) hmiddle
    rw [houterEq] at hspec
    exact hspec
  have hle : middleWidth ≤ d * y := by
    have hscaled :
        p * middleWidth ≤ p * (d * y) := by
      calc
        p * middleWidth = middleWidth * p := by ring
        _ ≤ sourceWidth * y := hinner
        _ = p * (d * y) := by rw [hpFactor]; ring
    exact Nat.le_of_mul_le_mul_left hscaled hp
  have hge : d * y ≤ middleWidth := by
    have hscaled :
        q * (d * y) ≤ q * middleWidth := by
      calc
        q * (d * y) = targetWidth * y := by rw [hqFactor]; ring
        _ ≤ middleWidth * q := houter
        _ = q * middleWidth := by ring
    exact Nat.le_of_mul_le_mul_left hscaled hq
  exact ⟨y, (Nat.le_antisymm hle hge).symm⟩

/-- Dividing two positive endpoints by their gcd gives a coprime pair. -/
theorem coprime_endpointQuotients
    {sourceWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth) :
    Nat.Coprime
      (sourceWidth / Nat.gcd sourceWidth targetWidth)
      (targetWidth / Nat.gcd sourceWidth targetWidth) := by
  let d := Nat.gcd sourceWidth targetWidth
  let p := sourceWidth / d
  let q := targetWidth / d
  let g := Nat.gcd p q
  have hdpos : 0 < d := by
    simpa [d] using endpointGcd_pos (targetWidth := targetWidth) hsource
  have hdp : d ∣ sourceWidth := by
    simpa [d] using Nat.gcd_dvd_left sourceWidth targetWidth
  have hdq : d ∣ targetWidth := by
    simpa [d] using Nat.gcd_dvd_right sourceWidth targetWidth
  have hpFactor : sourceWidth = d * p := by
    calc
      sourceWidth = (sourceWidth / d) * d :=
        (Nat.div_mul_cancel hdp).symm
      _ = d * p := by simp [p, Nat.mul_comm]
  have hqFactor : targetWidth = d * q := by
    calc
      targetWidth = (targetWidth / d) * d :=
        (Nat.div_mul_cancel hdq).symm
      _ = d * q := by simp [q, Nat.mul_comm]
  have hgp : g ∣ p := by
    simpa [g] using Nat.gcd_dvd_left p q
  have hgq : g ∣ q := by
    simpa [g] using Nat.gcd_dvd_right p q
  have hdgSource : d * g ∣ sourceWidth := by
    rcases hgp with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [hpFactor, ha]
    ring
  have hdgTarget : d * g ∣ targetWidth := by
    rcases hgq with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [hqFactor, hb]
    ring
  have hdgD : d * g ∣ d := by
    simpa [d] using Nat.dvd_gcd hdgSource hdgTarget
  rcases hdgD with ⟨c, hc⟩
  have hcancel : d * 1 = d * (g * c) := by
    calc
      d * 1 = d := by simp
      _ = (d * g) * c := hc
      _ = d * (g * c) := by ring
  have hone : 1 = g * c :=
    Nat.eq_of_mul_eq_mul_left hdpos hcancel
  have hgOne : g = 1 := Nat.dvd_one.mp ⟨c, hone⟩
  simpa [Nat.Coprime, d, p, q, g] using hgOne

/--
General necessity: global exactness implies two-generator semigroup membership.
-/
theorem mem_twoGeneratorSemigroup_of_globallyExactInsertion
    {sourceWidth middleWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (htarget : 0 < targetWidth)
    (hexact : GloballyExactInsertion
      sourceWidth middleWidth targetWidth) :
    InTwoGeneratorSemigroup sourceWidth targetWidth middleWidth := by
  let d := Nat.gcd sourceWidth targetWidth
  let p := sourceWidth / d
  let q := targetWidth / d
  have hdpos : 0 < d := by
    simpa [d] using endpointGcd_pos (targetWidth := targetWidth) hsource
  have hdp : d ∣ sourceWidth := by
    simpa [d] using Nat.gcd_dvd_left sourceWidth targetWidth
  have hdq : d ∣ targetWidth := by
    simpa [d] using Nat.gcd_dvd_right sourceWidth targetWidth
  have hdh : d ∣ middleWidth := by
    simpa [d] using
      endpointGcd_dvd_middle_of_globallyExactInsertion
        hsource hmiddle htarget hexact
  let h := middleWidth / d
  have hpFactor : sourceWidth = d * p := by
    calc
      sourceWidth = (sourceWidth / d) * d :=
        (Nat.div_mul_cancel hdp).symm
      _ = d * p := by simp [p, Nat.mul_comm]
  have hqFactor : targetWidth = d * q := by
    calc
      targetWidth = (targetWidth / d) * d :=
        (Nat.div_mul_cancel hdq).symm
      _ = d * q := by simp [q, Nat.mul_comm]
  have hhFactor : middleWidth = d * h := by
    calc
      middleWidth = (middleWidth / d) * d :=
        (Nat.div_mul_cancel hdh).symm
      _ = d * h := by simp [h, Nat.mul_comm]
  have hp : 0 < p := by
    apply Nat.pos_of_ne_zero
    intro hpzero
    rw [hpzero, Nat.mul_zero] at hpFactor
    omega
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hqzero
    rw [hqzero, Nat.mul_zero] at hqFactor
    omega
  have hh : 0 < h := by
    apply Nat.pos_of_ne_zero
    intro hhzero
    rw [hhzero, Nat.mul_zero] at hhFactor
    omega
  have hcoprime : Nat.Coprime p q := by
    simpa [d, p, q] using
      coprime_endpointQuotients
        (targetWidth := targetWidth) hsource
  have hnormalizedExact : GloballyExactInsertion p h q := by
    intro x
    calc
      insertionComposite p h q x =
          insertionComposite (d * p) (d * h) (d * q) x :=
        (insertionComposite_mul_common hdpos hp hh).symm
      _ = insertionComposite sourceWidth middleWidth targetWidth x := by
        rw [← hpFactor, ← hhFactor, ← hqFactor]
      _ = indexLift sourceWidth targetWidth x := hexact x
      _ = indexLift (d * p) (d * q) x := by
        rw [← hpFactor, ← hqFactor]
      _ = indexLift p q x := indexLift_mul_common hdpos hp
  obtain ⟨a, b, hab⟩ :=
    mem_twoGeneratorSemigroup_of_globallyExactInsertion_of_coprime
      hp hh hcoprime hnormalizedExact
  refine ⟨a, b, ?_⟩
  calc
    middleWidth = d * h := hhFactor
    _ = d * (a * p + b * q) := by rw [hab]
    _ = a * (d * p) + b * (d * q) := by ring
    _ = a * sourceWidth + b * targetWidth := by
      rw [← hpFactor, ← hqFactor]

/-- Complete characterization for arbitrary positive widths. -/
theorem globallyExactInsertion_iff_mem_twoGeneratorSemigroup
    {sourceWidth middleWidth targetWidth : ℕ}
    (hsource : 0 < sourceWidth)
    (hmiddle : 0 < middleWidth)
    (htarget : 0 < targetWidth) :
    GloballyExactInsertion sourceWidth middleWidth targetWidth ↔
      InTwoGeneratorSemigroup sourceWidth targetWidth middleWidth := by
  constructor
  · exact mem_twoGeneratorSemigroup_of_globallyExactInsertion
      hsource hmiddle htarget
  · exact globallyExactInsertion_of_mem_twoGeneratorSemigroup
      hsource hmiddle

end MagicCapacity
end CbsLean
