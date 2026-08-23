import Mathlib

open Finset
open Filter
open scoped BigOperators

namespace CbsLean

def weightedGap (a b : ℕ → ℕ) (L : ℕ) : ℕ :=
  ∑ i ∈ range L, (L - i) * (b i - a i)

def frontierMultiplicity (g : ℕ → ℕ) (L r : ℕ) : ℕ :=
  Nat.choose (g L) r

/--
Zero-indexed coffee bean shell counts.

Lean index `i` corresponds to the paper shell `\ell = i + 1`, so
`coffeeBeanShell k i = \binom{k + i - 1}{k - 1}` matches the paper formula
`g_\ell(T_{\mathrm{cb}}) = \binom{k + \ell - 2}{k - 1}`.
-/
def coffeeBeanShell (k : ℕ) (i : ℕ) : ℕ :=
  Nat.choose (k + i - 1) (k - 1)

def coffeeBeanCumulative (k L : ℕ) : ℕ :=
  ∑ i ∈ range L, coffeeBeanShell k i

def coffeeBeanOptimalMultiplicity (k L r : ℕ) : ℕ :=
  frontierMultiplicity (coffeeBeanShell k) L r

def coffeeBeanMainCost (k L : ℕ) : ℕ :=
  ∑ i ∈ range L, (i + 1) * coffeeBeanShell k i

theorem weightedGapZero_iff_lowerShellAgreement
    {a b : ℕ → ℕ} {L : ℕ}
    (hdom : ∀ i ∈ range L, a i ≤ b i) :
    weightedGap a b L = 0 ↔
      ∀ i ∈ range L, a i = b i := by
  constructor
  · intro hgap
    have hzero :
        ∀ i ∈ range L, (L - i) * (b i - a i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).1 hgap
    intro i hi
    have hprod : (L - i) * (b i - a i) = 0 := hzero i hi
    have hne : L - i ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (mem_range.mp hi))
    have hsub : b i - a i = 0 := (Nat.mul_eq_zero.mp hprod).resolve_left hne
    exact Nat.le_antisymm (hdom i hi) ((Nat.sub_eq_zero_iff_le).mp hsub)
  · intro hagree
    refine (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).2 ?_
    intro i hi
    simp [hagree i hi]

def EqualCostData (a b : ℕ → ℕ) (L r : ℕ) : Prop :=
  weightedGap a b L = 0 ∧ r ≤ a L

def EqualCostProfile (a b : ℕ → ℕ) (L r : ℕ) : Prop :=
  (∀ i ∈ range L, a i = b i) ∧ r ≤ a L

def CoffeeBeanEqualCostData (a : ℕ → ℕ) (k n L r : ℕ) : Prop :=
  EqualCostData a (coffeeBeanShell k) L r ∧ n = coffeeBeanCumulative k L + r

def CoffeeBeanEqualCostProfile (a : ℕ → ℕ) (k n L r : ℕ) : Prop :=
  EqualCostProfile a (coffeeBeanShell k) L r ∧ n = coffeeBeanCumulative k L + r

def CoffeeBeanClosedFormData (a : ℕ → ℕ) (k n L r : ℕ) : Prop :=
  EqualCostData a (coffeeBeanShell k) L r ∧ n = Nat.choose (k + L - 1) k + r

def CoffeeBeanClosedFormProfile (a : ℕ → ℕ) (k n L r : ℕ) : Prop :=
  EqualCostProfile a (coffeeBeanShell k) L r ∧ n = Nat.choose (k + L - 1) k + r

def CoffeeBeanLevelWindow (k n L : ℕ) : Prop :=
  coffeeBeanCumulative k L ≤ n ∧ n < coffeeBeanCumulative k (L + 1)

def coffeeBeanLevel (k n : ℕ) : ℕ :=
  Nat.findGreatest (fun L => coffeeBeanCumulative k L ≤ n) n

def coffeeBeanRemainder (k n : ℕ) : ℕ :=
  n - coffeeBeanCumulative k (coffeeBeanLevel k n)

def coffeeBeanMinCost (k n : ℕ) : ℕ :=
  coffeeBeanMainCost k (coffeeBeanLevel k n) +
    (coffeeBeanLevel k n + 1) * coffeeBeanRemainder k n

private theorem choose_shift_strictMono {r : ℕ} (hr : 0 < r) :
    StrictMono fun n => Nat.choose (n + r) r := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have hsucc :
      Nat.choose (n + 1 + r) r = Nat.choose (n + r) (r - 1) + Nat.choose (n + r) r := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.choose_succ_left (n + r) r hr)
  rw [hsucc]
  have hpos : 0 < Nat.choose (n + r) (r - 1) := by
    have hbound : r - 1 ≤ n + r := by
      omega
    apply Nat.choose_pos
    exact hbound
  exact Nat.lt_add_of_pos_left hpos

theorem frontierMultiplicity_eq_iff
    {a b r : ℕ} (hra : r ≤ a) (hab : a ≤ b) :
    Nat.choose a r = Nat.choose b r ↔ r = 0 ∨ a = b := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    constructor
    · intro hchoose
      right
      have hstrict := choose_shift_strictMono hrpos
      have hs : a - r = b - r := by
        apply hstrict.injective
        simpa [Nat.sub_add_cancel hra, Nat.sub_add_cancel (le_trans hra hab)] using hchoose
      omega
    · rintro (rfl | rfl)
      · contradiction
      · rfl

theorem frontierMultiplicity_le
    {g h : ℕ → ℕ} {L r : ℕ}
    (hgh : g L ≤ h L) :
    frontierMultiplicity g L r ≤ frontierMultiplicity h L r := by
  exact Nat.choose_le_choose r hgh

theorem frontierMultiplicity_eq_iff_of_le
    {g h : ℕ → ℕ} {L r : ℕ}
    (hr : r ≤ g L) (hgh : g L ≤ h L) :
    frontierMultiplicity g L r = frontierMultiplicity h L r ↔
      r = 0 ∨ g L = h L := by
  simpa [frontierMultiplicity] using frontierMultiplicity_eq_iff hr hgh

theorem equalCostData_iff_profile
    {a b : ℕ → ℕ} {L r : ℕ}
    (hdom : ∀ i ∈ range L, a i ≤ b i) :
    EqualCostData a b L r ↔ EqualCostProfile a b L r := by
  constructor
  · rintro ⟨hgap, hr⟩
    exact ⟨(weightedGapZero_iff_lowerShellAgreement hdom).1 hgap, hr⟩
  · rintro ⟨hagree, hr⟩
    exact ⟨(weightedGapZero_iff_lowerShellAgreement hdom).2 hagree, hr⟩

theorem frontierMultiplicity_le_of_equalCostData
    {a b : ℕ → ℕ} {L r : ℕ}
    (hfront : a L ≤ b L) :
    EqualCostData a b L r →
      frontierMultiplicity a L r ≤ frontierMultiplicity b L r := by
  intro _
  exact frontierMultiplicity_le hfront

theorem frontierMultiplicity_eq_iff_of_equalCostData
    {a b : ℕ → ℕ} {L r : ℕ}
    (hfront : a L ≤ b L) :
    EqualCostData a b L r →
      (frontierMultiplicity a L r = frontierMultiplicity b L r ↔
        r = 0 ∨ a L = b L) := by
  rintro ⟨_, hr⟩
  exact frontierMultiplicity_eq_iff_of_le hr hfront

theorem rigidityPackage
    {a b : ℕ → ℕ} {L r : ℕ}
    (hdom : ∀ i ∈ range L, a i ≤ b i)
    (hfront : a L ≤ b L) :
    (EqualCostData a b L r ↔ EqualCostProfile a b L r) ∧
      (EqualCostData a b L r →
        frontierMultiplicity a L r ≤ frontierMultiplicity b L r) ∧
      (EqualCostData a b L r →
        (frontierMultiplicity a L r = frontierMultiplicity b L r ↔
          r = 0 ∨ a L = b L)) := by
  refine ⟨equalCostData_iff_profile hdom, ?_, ?_⟩
  · exact frontierMultiplicity_le_of_equalCostData hfront
  · exact frontierMultiplicity_eq_iff_of_equalCostData hfront

theorem coffeeBeanCumulative_closedForm
    {k L : ℕ} (hk : 0 < k) :
    coffeeBeanCumulative k L = Nat.choose (k + L - 1) k := by
  rcases Nat.exists_eq_add_of_le' hk with ⟨k', rfl⟩
  cases L with
  | zero =>
      simp [coffeeBeanCumulative]
  | succ L =>
      simpa [
        coffeeBeanCumulative,
        coffeeBeanShell,
        Nat.add_assoc,
        Nat.add_left_comm,
        Nat.add_comm
      ] using
        (Nat.sum_range_add_choose L k')

theorem coffeeBeanEqualCostData_iff_closedForm
    {a : ℕ → ℕ} {k n L r : ℕ}
    (hk : 0 < k) :
    CoffeeBeanEqualCostData a k n L r ↔ CoffeeBeanClosedFormData a k n L r := by
  simp [CoffeeBeanEqualCostData, CoffeeBeanClosedFormData, coffeeBeanCumulative_closedForm hk]

theorem coffeeBeanEqualCostProfile_iff_closedForm
    {a : ℕ → ℕ} {k n L r : ℕ}
    (hk : 0 < k) :
    CoffeeBeanEqualCostProfile a k n L r ↔ CoffeeBeanClosedFormProfile a k n L r := by
  simp [CoffeeBeanEqualCostProfile, CoffeeBeanClosedFormProfile, coffeeBeanCumulative_closedForm hk]

theorem coffeeBeanCumulative_factorial_mul_bounds
    {k L : ℕ} (hk : 0 < k) :
    (L ^ k ≤ Nat.factorial k * coffeeBeanCumulative k L) ∧
      Nat.factorial k * coffeeBeanCumulative k L ≤ (L + k - 1) ^ k := by
  have hclosed := coffeeBeanCumulative_closedForm (k := k) (L := L) hk
  constructor
  · calc
      L ^ k = ((k + L - 1) + 1 - k) ^ k := by
        have hsub : (k + L - 1) + 1 - k = L := by
          omega
        simp [hsub]
      _ ≤ (k + L - 1).descFactorial k := Nat.pow_sub_le_descFactorial _ _
      _ = Nat.factorial k * Nat.choose (k + L - 1) k := by
        exact Nat.descFactorial_eq_factorial_mul_choose _ _
      _ = Nat.factorial k * coffeeBeanCumulative k L := by rw [hclosed]
  · calc
      Nat.factorial k * coffeeBeanCumulative k L =
          Nat.factorial k * Nat.choose (k + L - 1) k := by
        rw [hclosed]
      _ = (k + L - 1).descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ (k + L - 1) ^ k := Nat.descFactorial_le_pow _ _
      _ = (L + k - 1) ^ k := by rw [Nat.add_comm]

theorem coffeeBeanShell_le_pow
    {k L : ℕ} (hk : 0 < k) :
    coffeeBeanShell k L ≤ (L + k - 1) ^ (k - 1) := by
  rcases Nat.exists_eq_add_of_le' hk with ⟨k', rfl⟩
  simpa [coffeeBeanShell, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.choose_le_pow (L + k') k')

theorem coffeeBeanTopShellCost_le
    {k L r : ℕ}
    (hk : 0 < k)
    (hr : r ≤ coffeeBeanShell k L) :
    (L + 1) * r ≤ (L + 1) * (L + k - 1) ^ (k - 1) := by
  exact Nat.mul_le_mul_left _ (le_trans hr (coffeeBeanShell_le_pow hk))

theorem coffeeBeanTopShellCost_scale
    {k L r : ℕ}
    (hk : 0 < k)
    (hr : r ≤ coffeeBeanShell k L) :
    (L + 1) * r ≤ (L + k) ^ k := by
  calc
    (L + 1) * r ≤ (L + 1) * (L + k - 1) ^ (k - 1) := coffeeBeanTopShellCost_le hk hr
    _ ≤ (L + k) * (L + k) ^ (k - 1) := by
      exact Nat.mul_le_mul
        (by omega)
        (by simpa [Nat.add_comm] using Nat.pow_le_pow_left (by omega) (k - 1))
    _ = (L + k) ^ k := by
      cases k with
      | zero => contradiction
      | succ k =>
          simp [pow_succ, Nat.mul_comm]

@[simp] theorem coffeeBeanCumulative_succ
    {k L : ℕ} :
    coffeeBeanCumulative k (L + 1) =
      coffeeBeanCumulative k L + coffeeBeanShell k L := by
  simp [coffeeBeanCumulative, Finset.sum_range_succ]

theorem coffeeBeanShell_pos
    {k i : ℕ} (hk : 0 < k) :
    0 < coffeeBeanShell k i := by
  rcases Nat.exists_eq_add_of_le' hk with ⟨k', rfl⟩
  simpa [coffeeBeanShell, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.choose_pos (Nat.le_add_right k' i))

theorem coffeeBeanCumulative_ge_level
    {k L : ℕ} (hk : 0 < k) :
    L ≤ coffeeBeanCumulative k L := by
  induction L with
  | zero =>
      simp [coffeeBeanCumulative]
  | succ L ih =>
      rw [coffeeBeanCumulative_succ]
      calc
        L + 1 ≤ coffeeBeanCumulative k L + 1 := Nat.succ_le_succ ih
        _ ≤ coffeeBeanCumulative k L + coffeeBeanShell k L := by
          exact Nat.add_le_add_left (Nat.succ_le_of_lt (coffeeBeanShell_pos hk)) _

theorem coffeeBeanLevel_le
    {k n : ℕ} :
    coffeeBeanLevel k n ≤ n :=
  Nat.findGreatest_le n

theorem coffeeBeanLevel_spec
    {k n : ℕ} :
    coffeeBeanCumulative k (coffeeBeanLevel k n) ≤ n := by
  exact Nat.findGreatest_spec
    (P := fun L => coffeeBeanCumulative k L ≤ n)
    (m := 0)
    (by simp)
    (by simp [coffeeBeanCumulative])

theorem coffeeBeanLevelWindow_level
    {k n : ℕ} (hk : 0 < k) :
    CoffeeBeanLevelWindow k n (coffeeBeanLevel k n) := by
  refine ⟨coffeeBeanLevel_spec, ?_⟩
  by_cases hlt : coffeeBeanLevel k n < n
  · have hnot : ¬ coffeeBeanCumulative k (coffeeBeanLevel k n + 1) ≤ n := by
      exact Nat.findGreatest_is_greatest
        (P := fun L => coffeeBeanCumulative k L ≤ n)
        (by simpa [coffeeBeanLevel] using hlt)
        (Nat.succ_le_of_lt hlt)
    exact lt_of_not_ge hnot
  · have heq : coffeeBeanLevel k n = n := by
      exact le_antisymm coffeeBeanLevel_le (le_of_not_gt hlt)
    rw [heq]
    exact lt_of_lt_of_le (Nat.lt_succ_self n) (coffeeBeanCumulative_ge_level hk)

theorem coffeeBeanRemainder_eq
    {k n : ℕ} :
    coffeeBeanCumulative k (coffeeBeanLevel k n) + coffeeBeanRemainder k n = n := by
  unfold coffeeBeanRemainder
  exact Nat.add_sub_of_le coffeeBeanLevel_spec

theorem coffeeBeanRemainder_lt_shell
    {k n : ℕ} (hk : 0 < k) :
    coffeeBeanRemainder k n < coffeeBeanShell k (coffeeBeanLevel k n) := by
  have hwindow := coffeeBeanLevelWindow_level hk (k := k) (n := n)
  rcases hwindow with ⟨_, hupp⟩
  have hsum := coffeeBeanRemainder_eq (k := k) (n := n)
  rw [coffeeBeanCumulative_succ] at hupp
  have hlt :
      coffeeBeanCumulative k (coffeeBeanLevel k n) + coffeeBeanRemainder k n <
        coffeeBeanCumulative k (coffeeBeanLevel k n) +
          coffeeBeanShell k (coffeeBeanLevel k n) := by
    simpa [hsum] using hupp
  omega

theorem coffeeBeanRemainder_le_shell
    {k n : ℕ} (hk : 0 < k) :
    coffeeBeanRemainder k n ≤ coffeeBeanShell k (coffeeBeanLevel k n) := by
  exact Nat.le_of_lt (coffeeBeanRemainder_lt_shell hk)

private theorem succ_mul_coffeeBeanShell
    {k i : ℕ} (hk : 0 < k) :
    (i + 1) * coffeeBeanShell k i =
      coffeeBeanShell k i + k * Nat.choose (k + i - 1) k := by
  have hkpred : 1 + (k - 1) = k := by
    simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hk
  have hsub : (k + i - 1) - (k - 1) = i := by
    omega
  have hchoose :
      Nat.choose (k + i - 1) k * k =
        Nat.choose (k + i - 1) (k - 1) * i := by
    simpa [hkpred, hsub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.choose_succ_right_eq (k + i - 1) (k - 1))
  calc
    (i + 1) * coffeeBeanShell k i = i * coffeeBeanShell k i + coffeeBeanShell k i := by
      rw [Nat.add_mul, one_mul]
    _ = k * Nat.choose (k + i - 1) k + coffeeBeanShell k i := by
      rw [show i * coffeeBeanShell k i = k * Nat.choose (k + i - 1) k by
            simpa [coffeeBeanShell, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              hchoose.symm]
    _ = coffeeBeanShell k i + k * Nat.choose (k + i - 1) k := by
      rw [Nat.add_comm]

theorem coffeeBeanChooseTail_closedForm
    {k L : ℕ} (hk : 0 < k) :
    (∑ i ∈ range L, Nat.choose (k + i - 1) k) =
      Nat.choose (k + L - 1) (k + 1) := by
  induction L with
  | zero =>
      rw [sum_range_zero]
      symm
      exact Nat.choose_eq_zero_of_lt (by omega)
  | succ L ih =>
      rw [sum_range_succ, ih]
      have hs : k + L - 1 + 1 = k + L := by
        omega
      simpa [hs, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.choose_succ_succ' (k + L - 1) k).symm

theorem coffeeBeanMainCost_closedForm
    {k L : ℕ} (hk : 0 < k) :
    coffeeBeanMainCost k L =
      coffeeBeanCumulative k L + k * Nat.choose (k + L - 1) (k + 1) := by
  rw [coffeeBeanMainCost]
  have hsplit :
      (∑ i ∈ range L, (i + 1) * coffeeBeanShell k i) =
        ∑ i ∈ range L, (coffeeBeanShell k i + k * Nat.choose (k + i - 1) k) := by
    refine sum_congr rfl ?_
    intro i hi
    exact succ_mul_coffeeBeanShell hk
  rw [hsplit, sum_add_distrib, coffeeBeanCumulative, ← mul_sum]
  congr 1
  exact congrArg (fun x => k * x) (coffeeBeanChooseTail_closedForm hk)

private theorem pow_le_pow_succ_of_le
    {a b m : ℕ} (hab : a ≤ b) (hb : 1 ≤ b) :
    a ^ m ≤ b ^ (m + 1) := by
  refine (Nat.pow_le_pow_left hab m).trans ?_
  have hmul : b ^ m * 1 ≤ b ^ m * b := Nat.mul_le_mul_left _ hb
  simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

theorem coffeeBeanMainCost_factorial_mul_bounds
    {k L : ℕ} (hk : 0 < k) :
    (L - 1) ^ (k + 1) ≤ Nat.factorial (k + 1) * coffeeBeanMainCost k L ∧
      Nat.factorial (k + 1) * coffeeBeanMainCost k L ≤
        (2 * k + 1) * (L + k) ^ (k + 1) := by
  have hmain := coffeeBeanMainCost_closedForm (k := k) (L := L) hk
  have hchooseLower :
      (L - 1) ^ (k + 1) ≤ Nat.factorial (k + 1) * Nat.choose (k + L - 1) (k + 1) := by
    calc
      (L - 1) ^ (k + 1) = ((k + L - 1) + 1 - (k + 1)) ^ (k + 1) := by
        have hsub : (k + L - 1) + 1 - (k + 1) = L - 1 := by
          omega
        simp [hsub]
      _ ≤ (k + L - 1).descFactorial (k + 1) := Nat.pow_sub_le_descFactorial _ _
      _ = Nat.factorial (k + 1) * Nat.choose (k + L - 1) (k + 1) := by
        exact Nat.descFactorial_eq_factorial_mul_choose _ _
  have hchooseUpper :
      Nat.factorial (k + 1) * Nat.choose (k + L - 1) (k + 1) ≤
        (L + k) ^ (k + 1) := by
    calc
      Nat.factorial (k + 1) * Nat.choose (k + L - 1) (k + 1) =
          (k + L - 1).descFactorial (k + 1) := by
        exact (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ (k + L - 1) ^ (k + 1) := Nat.descFactorial_le_pow _ _
      _ ≤ (L + k) ^ (k + 1) := by
        simpa [Nat.add_comm] using Nat.pow_le_pow_left (by omega) (k + 1)
  constructor
  · have hchooseLeMain :
        Nat.choose (k + L - 1) (k + 1) ≤ coffeeBeanMainCost k L := by
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
      rw [hmain]
      have hmul :
          Nat.choose (k + L - 1) (k + 1) ≤
            k * Nat.choose (k + L - 1) (k + 1) := by
        simpa [one_mul] using
          Nat.mul_le_mul_right (Nat.choose (k + L - 1) (k + 1)) hk1
      exact hmul.trans (Nat.le_add_left _ _)
    exact hchooseLower.trans (Nat.mul_le_mul_left _ hchooseLeMain)
  · have hcumUpper :
        Nat.factorial (k + 1) * coffeeBeanCumulative k L ≤
          (k + 1) * (L + k) ^ (k + 1) := by
      calc
        Nat.factorial (k + 1) * coffeeBeanCumulative k L =
            (k + 1) * (Nat.factorial k * coffeeBeanCumulative k L) := by
          simp [Nat.factorial_succ, Nat.mul_assoc, Nat.mul_comm]
        _ ≤ (k + 1) * (L + k - 1) ^ k := by
          exact Nat.mul_le_mul_left _ <|
            (coffeeBeanCumulative_factorial_mul_bounds (k := k) (L := L) hk).2
        _ ≤ (k + 1) * (L + k) ^ (k + 1) := by
          exact Nat.mul_le_mul_left _ <|
            pow_le_pow_succ_of_le (by omega)
              (by
                have : 1 ≤ L + k := by omega
                exact this)
    have htailUpper :
        Nat.factorial (k + 1) * (k * Nat.choose (k + L - 1) (k + 1)) ≤
          k * (L + k) ^ (k + 1) := by
      calc
        Nat.factorial (k + 1) * (k * Nat.choose (k + L - 1) (k + 1)) =
            k * (Nat.factorial (k + 1) * Nat.choose (k + L - 1) (k + 1)) := by
          simp [Nat.mul_assoc, Nat.mul_comm]
        _ ≤ k * (L + k) ^ (k + 1) := Nat.mul_le_mul_left _ hchooseUpper
    rw [hmain, Nat.mul_add]
    calc
      Nat.factorial (k + 1) * coffeeBeanCumulative k L +
          Nat.factorial (k + 1) * (k * Nat.choose (k + L - 1) (k + 1)) ≤
            (k + 1) * (L + k) ^ (k + 1) + k * (L + k) ^ (k + 1) := by
        exact Nat.add_le_add hcumUpper htailUpper
      _ = (2 * k + 1) * (L + k) ^ (k + 1) := by
        rw [← Nat.add_mul]
        have hcoeff : (k + 1) + k = 2 * k + 1 := by
          omega
        rw [hcoeff]

theorem coffeeBeanMainCost_exact
    {k L : ℕ} (hk : 0 < k) :
    (k + 1) * coffeeBeanMainCost k L =
      (k * L + 1) * coffeeBeanCumulative k L := by
  have hmain := coffeeBeanMainCost_closedForm (k := k) (L := L) hk
  have hchoose :
      (k + 1) * Nat.choose (k + L - 1) (k + 1) =
        (L - 1) * Nat.choose (k + L - 1) k := by
    have hsub : k + L - 1 - k = L - 1 := by
      omega
    have hraw :=
      (Nat.choose_succ_right_eq (k + L - 1) k).symm
    simpa [hsub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm]
      using hraw.symm
  rw [hmain, Nat.mul_add]
  calc
    (k + 1) * coffeeBeanCumulative k L +
        (k + 1) * (k * Nat.choose (k + L - 1) (k + 1)) =
          (k + 1) * coffeeBeanCumulative k L +
            k * ((k + 1) * Nat.choose (k + L - 1) (k + 1)) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    _ = (k + 1) * coffeeBeanCumulative k L +
          k * ((L - 1) * Nat.choose (k + L - 1) k) := by
      rw [hchoose]
    _ = (k + 1) * Nat.choose (k + L - 1) k +
          k * ((L - 1) * Nat.choose (k + L - 1) k) := by
      rw [coffeeBeanCumulative_closedForm hk]
    _ = (k * L + 1) * Nat.choose (k + L - 1) k := by
      cases L with
      | zero =>
          have hzero : Nat.choose (k - 1) k = 0 := by
            exact Nat.choose_eq_zero_of_lt (by omega)
          simp [hzero]
      | succ L =>
          let c := Nat.choose (k + L) k
          have hmul : k * (L * c) = (k * L) * c := by
            simp [c, Nat.mul_assoc]
          have hsub : L + 1 - 1 = L := by omega
          rw [show Nat.choose (k + (L + 1) - 1) k = c by simp [c]]
          rw [hsub, hmul, ← Nat.add_mul]
          have hcoeff : k + 1 + k * L = k * (L + 1) + 1 := by
            calc
              k + 1 + k * L = k * L + k + 1 := by ac_rfl
              _ = k * (L + 1) + 1 := by rw [Nat.mul_add, Nat.mul_one]
          rw [hcoeff]
    _ = (k * L + 1) * coffeeBeanCumulative k L := by
      rw [coffeeBeanCumulative_closedForm hk]

theorem coffeeBeanMinCost_exact
    {k n : ℕ} (hk : 0 < k) :
    (k + 1) * coffeeBeanMinCost k n =
      (k * coffeeBeanLevel k n + 1) * n +
        (coffeeBeanLevel k n + k) * coffeeBeanRemainder k n := by
  let L := coffeeBeanLevel k n
  let r := coffeeBeanRemainder k n
  have hsum : coffeeBeanCumulative k L + r = n := by
    simpa [L, r] using coffeeBeanRemainder_eq (k := k) (n := n)
  unfold coffeeBeanMinCost
  calc
    (k + 1) *
        (coffeeBeanMainCost k (coffeeBeanLevel k n) +
          (coffeeBeanLevel k n + 1) * coffeeBeanRemainder k n) =
          (k + 1) * coffeeBeanMainCost k L + (k + 1) * ((L + 1) * r) := by
      simp [L, r, Nat.mul_add]
    _ = (k * L + 1) * coffeeBeanCumulative k L + (k + 1) * ((L + 1) * r) := by
      rw [coffeeBeanMainCost_exact hk]
    _ = (k * L + 1) * n + (L + k) * r := by
      rw [← hsum]
      ring_nf
    _ = (k * coffeeBeanLevel k n + 1) * n +
          (coffeeBeanLevel k n + k) * coffeeBeanRemainder k n := by
      simp [L, r, Nat.add_comm]

theorem coffeeBeanAsymptoticSkeleton
    {k L r : ℕ}
    (hk : 0 < k)
    (hr : r ≤ coffeeBeanShell k L) :
    (L - 1) ^ (k + 1) ≤ Nat.factorial (k + 1) * coffeeBeanMainCost k L ∧
      (L + 1) * r ≤ (L + k) ^ k := by
  exact ⟨(coffeeBeanMainCost_factorial_mul_bounds hk).1, coffeeBeanTopShellCost_scale hk hr⟩

theorem coffeeBeanLevelWindow_iff_closedForm
    {k n L : ℕ} (hk : 0 < k) :
    CoffeeBeanLevelWindow k n L ↔
      Nat.choose (k + L - 1) k ≤ n ∧ n < Nat.choose (k + L) k := by
  rw [
    CoffeeBeanLevelWindow,
    coffeeBeanCumulative_closedForm (k := k) (L := L) hk,
    coffeeBeanCumulative_closedForm (k := k) (L := L + 1) hk
  ]
  simp

theorem coffeeBeanLevelWindow_factorial_mul_bounds
    {k n L : ℕ} (hk : 0 < k)
    (hwindow : CoffeeBeanLevelWindow k n L) :
    L ^ k ≤ Nat.factorial k * n ∧ Nat.factorial k * n < (L + k) ^ k := by
  rcases hwindow with ⟨hlow, hupp⟩
  constructor
  · exact
      (coffeeBeanCumulative_factorial_mul_bounds (k := k) (L := L) hk).1.trans
        (Nat.mul_le_mul_left _ hlow)
  · have hmul :
        Nat.factorial k * n < Nat.factorial k * coffeeBeanCumulative k (L + 1) := by
      exact Nat.mul_lt_mul_of_pos_left hupp (Nat.factorial_pos k)
    exact hmul.trans_le <|
      by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (coffeeBeanCumulative_factorial_mul_bounds (k := k) (L := L + 1) hk).2

theorem coffeeBeanLevelWindow_realRootBounds
    {k n L : ℕ} (hk : 0 < k)
    (hwindow : CoffeeBeanLevelWindow k n L) :
    (L : ℝ) ≤ (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) ∧
      (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) < (L + k : ℝ) := by
  have hpow := coffeeBeanLevelWindow_factorial_mul_bounds hk hwindow
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hA0 : 0 ≤ ((Nat.factorial k * n : ℕ) : ℝ) := by positivity
  have hU0 : 0 ≤ (L + k : ℝ) := by positivity
  constructor
  · rw [Real.le_rpow_inv_iff_of_pos hL0 hA0 hkR]
    have hcast : ((L : ℝ) ^ k) ≤ ((Nat.factorial k * n : ℕ) : ℝ) := by
      exact_mod_cast hpow.1
    simpa [Real.rpow_natCast] using hcast
  · rw [Real.rpow_inv_lt_iff_of_pos hA0 hU0 hkR]
    have hcast : (((Nat.factorial k * n : ℕ) : ℝ) < (L + k : ℝ) ^ k) := by
      exact_mod_cast hpow.2
    simpa [Real.rpow_natCast] using hcast

theorem coffeeBeanMainCost_realBounds
    {k L : ℕ} (hk : 0 < k) :
    (((L - 1 : ℕ) : ℝ) ^ (k + 1 : ℕ)) ≤
      ((Nat.factorial (k + 1) * coffeeBeanMainCost k L : ℕ) : ℝ) ∧
      ((Nat.factorial (k + 1) * coffeeBeanMainCost k L : ℕ) : ℝ) ≤
        ((2 * k + 1 : ℕ) : ℝ) * ((L + k : ℝ) ^ (k + 1 : ℕ)) := by
  exact_mod_cast coffeeBeanMainCost_factorial_mul_bounds (k := k) (L := L) hk

theorem coffeeBeanTopShellCost_realScale
    {k L r : ℕ}
    (hk : 0 < k)
    (hr : r ≤ coffeeBeanShell k L) :
    (((L + 1) * r : ℕ) : ℝ) ≤ (L + k : ℝ) ^ (k : ℕ) := by
  exact_mod_cast coffeeBeanTopShellCost_scale (k := k) (L := L) (r := r) hk hr

theorem coffeeBeanLevel_realRootBounds
    {k n : ℕ} (hk : 0 < k) :
    let A := (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
    (coffeeBeanLevel k n : ℝ) ≤ A ∧ A < (coffeeBeanLevel k n + k : ℝ) := by
  simpa using
    (coffeeBeanLevelWindow_realRootBounds
      (k := k) (n := n) (L := coffeeBeanLevel k n) hk
      (coffeeBeanLevelWindow_level (k := k) (n := n) hk))

theorem coffeeBeanNormalization_eq
    {k n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) =
      ((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * (n : ℝ) ^ (1 + (k : ℝ)⁻¹) := by
  have hf0 : 0 ≤ (Nat.factorial k : ℝ) := by positivity
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (n : ℝ) * (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) =
        (n : ℝ) * (((Nat.factorial k : ℝ) * (n : ℝ)) ^ ((k : ℝ)⁻¹)) := by
      norm_num
    _ = (n : ℝ) * ((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹) * (n : ℝ) ^ ((k : ℝ)⁻¹)) := by
      rw [Real.mul_rpow hf0 hn0]
    _ = ((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((n : ℝ) * (n : ℝ) ^ ((k : ℝ)⁻¹)) := by
      ring
    _ = ((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((k : ℝ)⁻¹)) := by
      simp
    _ = ((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * (n : ℝ) ^ (1 + (k : ℝ)⁻¹) := by
      rw [← Real.rpow_add hnR]

theorem coffeeBeanRemainderTerm_le_pow
    {k n : ℕ} (hk : 0 < k) :
    (coffeeBeanLevel k n + k) * coffeeBeanRemainder k n ≤
      (coffeeBeanLevel k n + k) ^ k := by
  let L := coffeeBeanLevel k n
  let r := coffeeBeanRemainder k n
  have hr : r ≤ coffeeBeanShell k L := by
    simpa [L, r] using coffeeBeanRemainder_le_shell (k := k) (n := n) hk
  have hshell : coffeeBeanShell k L ≤ (L + k - 1) ^ (k - 1) := by
    simpa [L] using coffeeBeanShell_le_pow (k := k) (L := L) hk
  have hpow :
      (L + k - 1) ^ (k - 1) ≤ (L + k) ^ (k - 1) := by
    simpa [Nat.add_comm] using Nat.pow_le_pow_left (by omega) (k - 1)
  calc
    (L + k) * r ≤ (L + k) * ((L + k - 1) ^ (k - 1)) := by
      exact Nat.mul_le_mul_left _ (le_trans hr hshell)
    _ ≤ (L + k) * ((L + k) ^ (k - 1)) := by
      exact Nat.mul_le_mul_left _ hpow
    _ = (L + k) ^ k := by
      cases k with
      | zero => contradiction
      | succ k =>
          simp [pow_succ, Nat.mul_comm]

theorem coffeeBeanMinCost_normalized_squeeze
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    let A := (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
    ((((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A)) ≤
      (((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A)) ∧
      (((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A)) ≤
        ((((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A)) +
          ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A)))) := by
  let L := coffeeBeanLevel k n
  let A : ℝ := (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
  have hApos : 0 < A := by
    have hpos : 0 < (((Nat.factorial k * n : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (Nat.factorial_pos k) hn
    exact Real.rpow_pos_of_pos hpos _
  have heq :
      (k + 1) * coffeeBeanMinCost k n =
        (k * L + 1) * n + (L + k) * coffeeBeanRemainder k n := by
    simpa [L] using coffeeBeanMinCost_exact (k := k) (n := n) hk
  have hrem :
      (L + k) * coffeeBeanRemainder k n ≤ (L + k) ^ k := by
    simpa [L] using coffeeBeanRemainderTerm_le_pow (k := k) (n := n) hk
  have hlower :
      (k * L + 1) * n ≤ (k + 1) * coffeeBeanMinCost k n := by
    calc
      (k * L + 1) * n ≤ (k * L + 1) * n + (L + k) * coffeeBeanRemainder k n := by
        exact Nat.le_add_right _ _
      _ = (k + 1) * coffeeBeanMinCost k n := by simpa using heq.symm
  have hupper :
      (k + 1) * coffeeBeanMinCost k n ≤ (k * L + 1) * n + (L + k) ^ k := by
    calc
      (k + 1) * coffeeBeanMinCost k n =
          (k * L + 1) * n + (L + k) * coffeeBeanRemainder k n := heq
      _ ≤ (k * L + 1) * n + (L + k) ^ k := Nat.add_le_add_left hrem _
  constructor
  · have hk1ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hnne : (n : ℝ) ≠ 0 := by positivity
    have hAne : A ≠ 0 := hApos.ne'
    field_simp [hk1ne, hnne, hAne]
    exact_mod_cast hlower
  · have hk1ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hnne : (n : ℝ) ≠ 0 := by positivity
    have hAne : A ≠ 0 := hApos.ne'
    field_simp [hk1ne, hnne, hAne]
    have hupper' :
        coffeeBeanMinCost k n * (k + 1) * ((k + 1) * n) ≤
          n * ((k * L + 1) * ((k + 1) * n) + (k + 1) * (L + k) ^ k) := by
      calc
        coffeeBeanMinCost k n * (k + 1) * ((k + 1) * n) =
            ((k + 1) * n) * ((k + 1) * coffeeBeanMinCost k n) := by
          simp [Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ ((k + 1) * n) * ((k * L + 1) * n + (L + k) ^ k) := by
          exact Nat.mul_le_mul_left _ hupper
        _ = n * ((k * L + 1) * ((k + 1) * n) + (k + 1) * (L + k) ^ k) := by
          calc
            ((k + 1) * n) * ((k * L + 1) * n + (L + k) ^ k) =
                ((k + 1) * n) * ((k * L + 1) * n) + ((k + 1) * n) * (L + k) ^ k := by
              rw [Nat.mul_add]
            _ = n * ((k * L + 1) * ((k + 1) * n)) + n * ((k + 1) * (L + k) ^ k) := by
              simp [Nat.mul_left_comm, Nat.mul_comm]
            _ = n * ((k * L + 1) * ((k + 1) * n) + (k + 1) * (L + k) ^ k) := by
              rw [Nat.mul_add]
    exact_mod_cast hupper'

theorem coffeeBeanScale_tendsto_atTop
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) atTop atTop := by
  have hkInv : 0 < (k : ℝ)⁻¹ := by positivity
  have hbase : Tendsto (fun n : ℕ => (Nat.factorial k : ℝ) * n) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hbase' : Tendsto (fun n : ℕ => (((Nat.factorial k * n : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hbase
  exact (tendsto_rpow_atTop hkInv).comp hbase'

theorem coffeeBeanScale_inv_tendsto_zero
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => ((((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))⁻¹)) atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp (coffeeBeanScale_tendsto_atTop hk)

theorem coffeeBeanConst_div_scale_tendsto_zero
    {k : ℕ} (hk : 0 < k) (c : ℝ) :
    Tendsto
      (fun n : ℕ => c / (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)))
      atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using
    (Tendsto.const_mul c (coffeeBeanScale_inv_tendsto_zero (k := k) hk))

theorem coffeeBeanLevel_div_scale_tendsto_one
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        (coffeeBeanLevel k n : ℝ) / (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)))
      atTop (nhds 1) := by
  let A : ℕ → ℝ := fun n => (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
  have hInv : Tendsto (fun n : ℕ => (A n)⁻¹) atTop (nhds 0) := by
    simpa [A] using coffeeBeanScale_inv_tendsto_zero (k := k) hk
  have hkDiv : Tendsto (fun n : ℕ => (k : ℝ) / A n) atTop (nhds 0) := by
    simpa [A, div_eq_mul_inv] using (tendsto_const_nhds.mul hInv)
  have hLower :
      Tendsto (fun n : ℕ => 1 - (k : ℝ) / A n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hkDiv
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        1 - (k : ℝ) / A n ≤ (coffeeBeanLevel k n : ℝ) / A n ∧
          (coffeeBeanLevel k n : ℝ) / A n ≤ 1 := by
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hroot :
        (coffeeBeanLevel k n : ℝ) ≤ A n ∧ A n < (coffeeBeanLevel k n + k : ℝ) := by
      simpa [A] using coffeeBeanLevel_realRootBounds (k := k) (n := n) hk
    rcases hroot with ⟨hLleA, hAlt⟩
    have hApos : 0 < A n := by
      have hpos : 0 < (((Nat.factorial k * n : ℕ) : ℝ)) := by
        exact_mod_cast Nat.mul_pos (Nat.factorial_pos k) hn
      exact Real.rpow_pos_of_pos hpos _
    have hupper : (coffeeBeanLevel k n : ℝ) / A n ≤ 1 := by
      apply (div_le_iff₀ hApos).2
      simpa using hLleA
    have hdiv :
        (1 : ℝ) < (k : ℝ) / A n + (coffeeBeanLevel k n : ℝ) / A n := by
      have hraw : A n / A n < (coffeeBeanLevel k n + k : ℝ) / A n := by
        exact div_lt_div_of_pos_right hAlt hApos
      have hunit : A n / A n = 1 := by
        field_simp [hApos.ne']
      rw [hunit] at hraw
      simpa [A, add_div, Nat.cast_add, add_comm, add_left_comm, add_assoc] using hraw
    have hlower : 1 - (k : ℝ) / A n ≤ (coffeeBeanLevel k n : ℝ) / A n := by
      nlinarith
    exact ⟨hlower, hupper⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLower tendsto_const_nhds
    (hEventually.mono fun _ h => h.1)
    (hEventually.mono fun _ h => h.2)

theorem coffeeBeanLowerNormalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) /
          (((k + 1 : ℕ) : ℝ) * (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)))))
      atTop (nhds ((k : ℝ) / (k + 1))) := by
  let A : ℕ → ℝ := fun n => (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
  have hEq :
      (fun n : ℕ =>
        (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A n))) =ᶠ[atTop]
      (fun n : ℕ =>
        ((k : ℝ) / (k + 1)) * ((coffeeBeanLevel k n : ℝ) / A n) +
          ((1 : ℝ) / (k + 1)) * ((1 : ℝ) / A n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hApos : 0 < A n := by
      have hpos : 0 < (((Nat.factorial k * n : ℕ) : ℝ)) := by
        exact_mod_cast Nat.mul_pos (Nat.factorial_pos k) hn
      exact Real.rpow_pos_of_pos hpos _
    have hk1ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hAne : A n ≠ 0 := hApos.ne'
    field_simp [hk1ne, hAne]
    all_goals try nlinarith
    have hcast :
        (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ)) =
          (k : ℝ) * (coffeeBeanLevel k n : ℝ) + 1 := by
      norm_num
    have hk1cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      norm_num
    rw [hcast, hk1cast]
    ring
  have hLevel : Tendsto (fun n : ℕ => (coffeeBeanLevel k n : ℝ) / A n) atTop (nhds 1) := by
    simpa [A] using coffeeBeanLevel_div_scale_tendsto_one (k := k) hk
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / A n) atTop (nhds 0) := by
    simpa [A] using coffeeBeanConst_div_scale_tendsto_zero (k := k) hk (1 : ℝ)
  have hSum :
      Tendsto
        (fun n : ℕ =>
          ((k : ℝ) / (k + 1)) * ((coffeeBeanLevel k n : ℝ) / A n) +
            ((1 : ℝ) / (k + 1)) * ((1 : ℝ) / A n))
        atTop (nhds (((k : ℝ) / (k + 1)) * 1 + ((1 : ℝ) / (k + 1)) * 0)) := by
    exact Tendsto.add (Tendsto.const_mul ((k : ℝ) / (k + 1)) hLevel)
      (Tendsto.const_mul ((1 : ℝ) / (k + 1)) hInv)
  simpa [A] using hSum.congr' hEq.symm

theorem coffeeBeanScale_pow_eq
    {k n : ℕ} (hk : 0 < k) :
    ((((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) ^ (k : ℕ)) =
      ((Nat.factorial k * n : ℕ) : ℝ) := by
  have hx : 0 ≤ (((Nat.factorial k * n : ℕ) : ℝ)) := by positivity
  have hkne : (k : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hmul : (k : ℝ)⁻¹ * k = 1 := by field_simp [hkne]
  rw [hmul, Real.rpow_one]

theorem coffeeBeanUpperError_tendsto_zero
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
          ((((k + 1) * n : ℕ) : ℝ) *
            (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)))))
      atTop (nhds 0) := by
  let A : ℕ → ℝ := fun n => (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
  have hA : Tendsto A atTop atTop := by
    simpa [A] using coffeeBeanScale_tendsto_atTop (k := k) hk
  have hABig : ∀ᶠ n : ℕ in atTop, (k : ℝ) ≤ A n := by
    exact hA.eventually_ge_atTop (k : ℝ)
  have hMajor :
      ∀ᶠ n : ℕ in atTop,
        0 ≤ ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A n)) ∧
          ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A n)) ≤
            ((((2 : ℝ) ^ (k : ℕ)) * (Nat.factorial k : ℝ)) / (k + 1)) / A n := by
    filter_upwards [eventually_ge_atTop 1, hABig] with n hn hAk
    have hApos : 0 < A n := by
      have hpos : 0 < (((Nat.factorial k * n : ℕ) : ℝ)) := by
        exact_mod_cast Nat.mul_pos (Nat.factorial_pos k) hn
      exact Real.rpow_pos_of_pos hpos _
    have hroot :
        (coffeeBeanLevel k n : ℝ) ≤ A n ∧ A n < (coffeeBeanLevel k n + k : ℝ) := by
      simpa [A] using coffeeBeanLevel_realRootBounds (k := k) (n := n) hk
    have hLk_le : (coffeeBeanLevel k n + k : ℝ) ≤ 2 * A n := by
      nlinarith [hroot.1, hAk]
    have hpow_le :
        (((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) ≤ (2 * A n) ^ (k : ℕ) := by
      have hcast :
          (((coffeeBeanLevel k n + k : ℕ) : ℝ)) =
            (coffeeBeanLevel k n + k : ℝ) := by
        norm_num
      rw [hcast]
      gcongr
    have hnonneg :
        0 ≤ ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A n)) := by
      positivity
    have hUpper :
        ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A n)) ≤
          ((((2 : ℝ) ^ (k : ℕ)) * (Nat.factorial k : ℝ)) / (k + 1)) / A n := by
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hk1ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      calc
        ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A n)) ≤
              ((2 * A n) ^ (k : ℕ)) / ((((k + 1) * n : ℕ) : ℝ) * A n) := by
          exact div_le_div_of_nonneg_right hpow_le (by positivity)
        _ = ((((2 : ℝ) ^ (k : ℕ)) * (Nat.factorial k : ℝ)) / (k + 1)) / A n := by
          rw [mul_pow, coffeeBeanScale_pow_eq (k := k) (n := n) hk]
          field_simp [hk1ne, hnR, hApos.ne']
          have hcast1 : (((Nat.factorial k * n : ℕ) : ℝ)) = (Nat.factorial k : ℝ) * n := by
            norm_num
          have hcast2 : ((((k + 1) * n : ℕ) : ℝ)) = (((k + 1 : ℕ) : ℝ) * n) := by
            norm_num
          have hcast3 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
            norm_num
          rw [hcast1, hcast2, hcast3]
          ring
    exact ⟨hnonneg, hUpper⟩
  have hUpperLim :
      Tendsto (fun n : ℕ => ((((2 : ℝ) ^ (k : ℕ)) * (Nat.factorial k : ℝ)) / (k + 1)) / A n)
        atTop (nhds 0) := by
    simpa [A] using
      coffeeBeanConst_div_scale_tendsto_zero
        (k := k) hk ((((2 : ℝ) ^ (k : ℕ)) * (Nat.factorial k : ℝ)) / (k + 1))
  exact squeeze_zero'
    (hMajor.mono fun _ h => h.1)
    (hMajor.mono fun _ h => h.2)
    hUpperLim

theorem coffeeBeanMinCost_div_scale_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        ((coffeeBeanMinCost k n : ℕ) : ℝ) /
          ((n : ℝ) * (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))))
      atTop (nhds ((k : ℝ) / (k + 1))) := by
  let A : ℕ → ℝ := fun n => (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
  have hLower :
      Tendsto
        (fun n : ℕ =>
          (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A n)))
        atTop (nhds ((k : ℝ) / (k + 1))) := by
    simpa [A] using coffeeBeanLowerNormalized_tendsto (k := k) hk
  have hErr :
      Tendsto
        (fun n : ℕ =>
          ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
            ((((k + 1) * n : ℕ) : ℝ) * A n)))
        atTop (nhds 0) := by
    simpa [A] using coffeeBeanUpperError_tendsto_zero (k := k) hk
  have hUpper :
      Tendsto
        (fun n : ℕ =>
          (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A n)) +
            ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
              ((((k + 1) * n : ℕ) : ℝ) * A n)))
        atTop (nhds ((k : ℝ) / (k + 1))) := by
    simpa using Tendsto.add hLower hErr
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A n)) ≤
          ((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A n) ∧
        ((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A n) ≤
          (((k * coffeeBeanLevel k n + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * A n)) +
            ((((coffeeBeanLevel k n + k : ℕ) : ℝ) ^ (k : ℕ)) /
              ((((k + 1) * n : ℕ) : ℝ) * A n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [A] using coffeeBeanMinCost_normalized_squeeze (k := k) (n := n) hk hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLower hUpper
    (hEventually.mono fun _ h => h.1)
    (hEventually.mono fun _ h => h.2)

theorem coffeeBeanMinCost_div_pow_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun n : ℕ =>
        ((coffeeBeanMinCost k n : ℕ) : ℝ) / (n : ℝ) ^ (1 + (k : ℝ)⁻¹))
      atTop (nhds (((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1)))) := by
  let A : ℕ → ℝ := fun n => (((Nat.factorial k * n : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))
  let c : ℝ := (Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)
  let α : ℝ := 1 + (k : ℝ)⁻¹
  have hcpos : 0 < c := by
    have hfac : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact Real.rpow_pos_of_pos hfac _
  have hScale :
      Tendsto
        (fun n : ℕ =>
          c * (((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A n)))
        atTop (nhds (c * ((k : ℝ) / (k + 1)))) := by
    have hbase : Tendsto
        (fun n : ℕ => ((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A n))
        atTop (nhds ((k : ℝ) / (k + 1))) := by
      simpa [A] using coffeeBeanMinCost_div_scale_tendsto (k := k) hk
    exact Tendsto.const_mul c hbase
  have hEq :
      (fun n : ℕ =>
        ((coffeeBeanMinCost k n : ℕ) : ℝ) / (n : ℝ) ^ α) =ᶠ[atTop]
      (fun n : ℕ =>
        c * (((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A n))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnorm : (n : ℝ) * A n = c * (n : ℝ) ^ α := by
      simpa [A, c, α] using coffeeBeanNormalization_eq (k := k) (n := n) hn
    calc
      ((coffeeBeanMinCost k n : ℕ) : ℝ) / (n : ℝ) ^ α
          = c * (((coffeeBeanMinCost k n : ℕ) : ℝ) / (c * (n : ℝ) ^ α)) := by
            field_simp [hcpos.ne', hnR.ne']
      _ = c * (((coffeeBeanMinCost k n : ℕ) : ℝ) / ((n : ℝ) * A n)) := by
            rw [hnorm]
  simpa [A, c, α] using hScale.congr' hEq.symm

theorem coffeeBeanMinCost_isEquivalent
    {k : ℕ} (hk : 0 < k) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => ((coffeeBeanMinCost k n : ℕ) : ℝ))
      (fun n : ℕ =>
        (((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1))) *
          (n : ℝ) ^ (1 + (k : ℝ)⁻¹)) := by
  let C : ℝ := ((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1))
  let α : ℝ := 1 + (k : ℝ)⁻¹
  have hCpos : 0 < C := by
    have hfac : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hfrac : 0 < (k : ℝ) / (k + 1) := by
      exact div_pos hkR (by positivity)
    exact mul_pos (Real.rpow_pos_of_pos hfac _) hfrac
  have hz :
      ∀ᶠ n : ℕ in atTop,
        (((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1))) *
            (n : ℝ) ^ (1 + (k : ℝ)⁻¹) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpow : 0 < (n : ℝ) ^ α := by
      exact Real.rpow_pos_of_pos hnR _
    simpa [C, α] using (mul_pos hCpos hpow).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
  have hbase :
      Tendsto
        (fun n : ℕ =>
          ((coffeeBeanMinCost k n : ℕ) : ℝ) / (n : ℝ) ^ α)
        atTop (nhds C) := by
    simpa [C, α, mul_comm, mul_left_comm, mul_assoc] using
      coffeeBeanMinCost_div_pow_tendsto (k := k) hk
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          C⁻¹ * (((coffeeBeanMinCost k n : ℕ) : ℝ) / (n : ℝ) ^ α))
        atTop (nhds (C⁻¹ * C)) := by
    exact Tendsto.const_mul C⁻¹ hbase
  have hCinv : C⁻¹ * C = 1 := by
    field_simp [hCpos.ne']
  have hEq :
      (fun n : ℕ =>
        ((coffeeBeanMinCost k n : ℕ) : ℝ) /
          ((((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1))) *
            (n : ℝ) ^ (1 + (k : ℝ)⁻¹))) =ᶠ[atTop]
      (fun n : ℕ =>
        C⁻¹ * (((coffeeBeanMinCost k n : ℕ) : ℝ) / (n : ℝ) ^ α)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    simp [C, α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hratio :
      Tendsto
        (fun n : ℕ =>
          ((coffeeBeanMinCost k n : ℕ) : ℝ) /
            ((((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1))) *
              (n : ℝ) ^ (1 + (k : ℝ)⁻¹)))
        atTop (nhds 1) := by
    have htmp :
        Tendsto
          (fun n : ℕ =>
            ((coffeeBeanMinCost k n : ℕ) : ℝ) /
              ((((Nat.factorial k : ℝ) ^ ((k : ℝ)⁻¹)) * ((k : ℝ) / (k + 1))) *
                (n : ℝ) ^ (1 + (k : ℝ)⁻¹)))
          atTop (nhds (C⁻¹ * C)) := by
      exact hscaled.congr' hEq.symm
    simpa [hCinv] using htmp
  exact hratio

theorem coffeeBeanRigidity
    {a : ℕ → ℕ} {k n L r : ℕ}
    (hdom : ∀ i ∈ range L, a i ≤ coffeeBeanShell k i)
    (hfront : a L ≤ coffeeBeanShell k L) :
    (CoffeeBeanEqualCostData a k n L r ↔
      CoffeeBeanEqualCostProfile a k n L r) ∧
      (CoffeeBeanEqualCostData a k n L r →
        frontierMultiplicity a L r ≤ coffeeBeanOptimalMultiplicity k L r) ∧
      (CoffeeBeanEqualCostData a k n L r →
        (frontierMultiplicity a L r = coffeeBeanOptimalMultiplicity k L r ↔
          r = 0 ∨ a L = coffeeBeanShell k L)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hdata, hn⟩
      exact ⟨(equalCostData_iff_profile hdom).1 hdata, hn⟩
    · rintro ⟨hprofile, hn⟩
      exact ⟨(equalCostData_iff_profile hdom).2 hprofile, hn⟩
  · rintro ⟨hdata, _⟩
    simpa [coffeeBeanOptimalMultiplicity] using
      frontierMultiplicity_le_of_equalCostData hfront hdata
  · rintro ⟨hdata, _⟩
    simpa [coffeeBeanOptimalMultiplicity] using
      frontierMultiplicity_eq_iff_of_equalCostData hfront hdata

theorem coffeeBeanRigidity_closedForm
    {a : ℕ → ℕ} {k n L r : ℕ}
    (hk : 0 < k)
    (hdom : ∀ i ∈ range L, a i ≤ coffeeBeanShell k i)
    (hfront : a L ≤ coffeeBeanShell k L) :
    (CoffeeBeanClosedFormData a k n L r ↔
      CoffeeBeanClosedFormProfile a k n L r) ∧
      (CoffeeBeanClosedFormData a k n L r →
        frontierMultiplicity a L r ≤ coffeeBeanOptimalMultiplicity k L r) ∧
      (CoffeeBeanClosedFormData a k n L r →
        (frontierMultiplicity a L r = coffeeBeanOptimalMultiplicity k L r ↔
          r = 0 ∨ a L = coffeeBeanShell k L)) := by
  have hrigid :
      (CoffeeBeanEqualCostData a k n L r ↔ CoffeeBeanEqualCostProfile a k n L r) ∧
        (CoffeeBeanEqualCostData a k n L r →
          frontierMultiplicity a L r ≤ coffeeBeanOptimalMultiplicity k L r) ∧
        (CoffeeBeanEqualCostData a k n L r →
          (frontierMultiplicity a L r = coffeeBeanOptimalMultiplicity k L r ↔
            r = 0 ∨ a L = coffeeBeanShell k L)) :=
    coffeeBeanRigidity (n := n) (r := r) hdom hfront
  refine ⟨?_, ?_, ?_⟩
  · rw [← coffeeBeanEqualCostData_iff_closedForm hk, ← coffeeBeanEqualCostProfile_iff_closedForm hk]
    exact hrigid.1
  · intro hdata
    exact hrigid.2.1 ((coffeeBeanEqualCostData_iff_closedForm hk).2 hdata)
  · intro hdata
    exact hrigid.2.2 ((coffeeBeanEqualCostData_iff_closedForm hk).2 hdata)

end CbsLean
