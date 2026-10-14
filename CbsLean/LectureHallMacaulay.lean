import CbsLean.NestedChains

/-!
# Lecture hall polytopes: the Macaulay-type lower bound in the dimension (paper §5)

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), §6: the Macaulay inequalities of Corollary 6.1 (the forms for general words and
the complement bound `Φ_D` in that corollary are not formalized here).

## Conventions

* `s : ℕ → ℕ` is the width sequence with `s 0 = s_1, s 1 = s_2, …` (indices shifted by one).
  A lattice point of `P_{(s_1, …, s_D)}` is stored by its numerators `x : Fin D → ℕ`, with
  `x j ≤ s j` and `x j * s (j + 1) ≤ x (j + 1) * s j` (i.e. `x_j / s_j ≤ x_{j+1} / s_{j+1}`).
* `lhEnds s i x` counts the points of dimension `i + 1` whose last numerator is `x`;
  `lhClosed s D` and `lhHalfOpen s D` are the paper's `h_s(D)` and `h°_s(D)` (both `1` at
  `D = 0`).  `lhClosed_eq_card` and `lhHalfOpen_eq_card` identify them with the numbers of
  lattice points.
* `ceilStep s i x = ⌈x · s(i+1) / s i⌉` is the ceiling map `c_i` of the paper on numerators, and
  `lift s n i` is `π_i` (lift from level `i` to level `n`).  `lhSets s n i = π_i(G_i)` is the
  nested sequence of the proof (constant from level `n` on) and `lhHalfSets` removes the common
  maximum `s n`.

## Main results

| paper | Lean |
|---|---|
| `c_i` is the least element `≥ g` | `ceilStep_le_iff` |
| `c_i` strictly increasing | `ceilStep_strictMono` |
| `(A_i)` nested | `lhSets_mono`, `lhHalfSets_mono` |
| bijection points ↔ multichains (as count identities) | `ends_lhSets`, `h_lhSets`, `h_lhHalfSets` |
| Corollary 6.1, `h_s` | `lh_reverse_macaulay` |
| Corollary 6.1, `h°_s` | `lh_reverse_macaulay_halfOpen` |
| Corollary 6.1, `h_s`, finite prefix | `lh_reverse_macaulay_of_prefix` |
| Corollary 6.1, `h°_s`, finite prefix | `lh_reverse_macaulay_halfOpen_of_prefix` |
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace LectureHall

open Macaulay NestedChains PathCount

/-! ### Lattice points and their counts -/

/-- The numerator grid `{0, …, s i}` at level `i`. -/
def grid (s : ℕ → ℕ) (i : ℕ) : Finset ℕ := range (s i + 1)

/-- Ratio order between consecutive levels: `x / s i ≤ y / s (i + 1)`. -/
def ratioLE (s : ℕ → ℕ) (i x y : ℕ) : Prop := x * s (i + 1) ≤ y * s i

instance (s : ℕ → ℕ) (i : ℕ) : DecidableRel (ratioLE s i) := fun x y =>
  inferInstanceAs (Decidable (x * s (i + 1) ≤ y * s i))

/-- Number of lattice points of `P_{(s_1, …, s_{i+1})}` with last numerator `x`. -/
def lhEnds (s : ℕ → ℕ) (i x : ℕ) : ℕ := pathEnds (grid s) (ratioLE s) i x

/-- Closed counts `h_s(D) = #(P_{(s_1,…,s_D)} ∩ ℤ^D)`. -/
def lhClosed (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => ∑ y ∈ range (s d + 1), lhEnds s d y

/-- Half-open counts `h°_s(D)` (last ratio `< 1`). -/
def lhHalfOpen (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => ∑ y ∈ range (s d), lhEnds s d y

/-- Lattice points of `P_{(s_1, …, s_{d+1})}`, as numerator vectors. -/
def lhPoints (s : ℕ → ℕ) (d : ℕ) : Finset (Fin (d + 1) → ℕ) := paths (grid s) (ratioLE s) d

theorem lhEnds_zero (s : ℕ → ℕ) (x : ℕ) : lhEnds s 0 x = if x ≤ s 0 then 1 else 0 := by
  simp only [lhEnds, pathEnds, grid, Finset.mem_range, Nat.lt_succ_iff]

theorem lhEnds_succ (s : ℕ → ℕ) (i y : ℕ) :
    lhEnds s (i + 1) y = if y ≤ s (i + 1) then
      ∑ x ∈ (range (s i + 1)).filter (fun x => x * s (i + 1) ≤ y * s i), lhEnds s i x
    else 0 := by
  simp only [lhEnds, pathEnds, grid, Finset.mem_range, Nat.lt_succ_iff]
  rfl

theorem lhClosed_eq_card (s : ℕ → ℕ) (d : ℕ) : lhClosed s (d + 1) = (lhPoints s d).card := by
  rw [lhPoints, PathCount.card_paths]
  rfl

theorem lhHalfOpen_eq_card (s : ℕ → ℕ) (d : ℕ) :
    lhHalfOpen s (d + 1) = ((lhPoints s d).filter (fun x => x (Fin.last d) < s d)).card := by
  rw [lhHalfOpen.eq_2, Finset.card_eq_sum_card_fiberwise (f := fun q => q (Fin.last d))
    (t := range (s d))]
  · refine Finset.sum_congr rfl fun y hy => ?_
    rw [lhPoints, Finset.filter_filter, lhEnds, ← PathCount.card_paths_last]
    congr 1
    refine Finset.filter_congr fun q _ => ?_
    constructor
    · intro h
      exact ⟨h ▸ Finset.mem_range.1 hy, h⟩
    · rintro ⟨-, h⟩
      exact h
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter] at hq
    exact Finset.mem_range.2 hq.2

/-- A closed point either has last ratio `< 1` or ends with all ratios `= 1`. -/
theorem lhClosed_succ (s : ℕ → ℕ) (d : ℕ) :
    lhClosed s (d + 1) = lhHalfOpen s (d + 1) + lhClosed s d := by
  rw [lhClosed.eq_2, lhHalfOpen.eq_2, Finset.sum_range_succ]
  congr 1
  cases d with
  | zero => rw [lhEnds_zero, if_pos le_rfl, lhClosed.eq_1]
  | succ m =>
    rw [lhEnds_succ, if_pos le_rfl, lhClosed.eq_2, Finset.filter_true_of_mem]
    intro x hx
    rw [Finset.mem_range] at hx
    calc x * s (m + 1) ≤ s m * s (m + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = s (m + 1) * s m := Nat.mul_comm _ _

/-! ### The ceiling maps -/

/-- The ceiling map `c_i(x) = ⌈x · s(i+1) / s i⌉` on numerators. -/
def ceilStep (s : ℕ → ℕ) (i x : ℕ) : ℕ := (x * s (i + 1) + s i - 1) / s i

section ceil

variable {s : ℕ → ℕ}

theorem ceilStep_le_iff {i : ℕ} (hs : 0 < s i) (x y : ℕ) :
    ceilStep s i x ≤ y ↔ x * s (i + 1) ≤ y * s i := by
  unfold ceilStep
  rw [Nat.div_le_iff_le_mul_add_pred hs, Nat.mul_comm (s i) y]
  omega

theorem ceilStep_strictMono {i : ℕ} (hs : 0 < s i) (hle : s i ≤ s (i + 1)) :
    StrictMono (ceilStep s i) := by
  refine strictMono_nat_of_lt_succ fun x => ?_
  by_contra h
  rw [not_lt, ceilStep_le_iff hs] at h
  have h1 : ceilStep s i x * s i ≤ x * s (i + 1) + s i - 1 := Nat.div_mul_le_self _ _
  have h2 : (x + 1) * s (i + 1) = x * s (i + 1) + s (i + 1) := Nat.succ_mul x (s (i + 1))
  omega

theorem ceilStep_self {i : ℕ} (hs : 0 < s i) : ceilStep s i (s i) = s (i + 1) := by
  unfold ceilStep
  rw [Nat.add_sub_assoc (by omega : 1 ≤ s i), Nat.mul_add_div hs,
    Nat.div_eq_of_lt (Nat.sub_lt hs Nat.one_pos), Nat.add_zero]

end ceil

/-- Lift by `k` ceiling steps starting at level `i`. -/
def liftK (s : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k + 1, i, x => liftK s k (i + 1) (ceilStep s i x)

/-- The lift `π_i` from level `i` to level `n` (identity for `n ≤ i`). -/
def lift (s : ℕ → ℕ) (n i x : ℕ) : ℕ := liftK s (n - i) i x

section lift

variable {s : ℕ → ℕ} (hpos : ∀ i, 0 < s i) (hmono : Monotone s)
include hpos

omit hpos in
theorem lift_of_le {n i : ℕ} (h : n ≤ i) (x : ℕ) : lift s n i x = x := by
  unfold lift
  rw [Nat.sub_eq_zero_of_le h]
  rfl

omit hpos in
theorem lift_succ {n i : ℕ} (h : i < n) (x : ℕ) :
    lift s n i x = lift s n (i + 1) (ceilStep s i x) := by
  unfold lift
  rw [(by omega : n - i = n - (i + 1) + 1)]
  rfl

include hmono in
theorem lift_strictMono (n i : ℕ) : StrictMono (lift s n i) := by
  unfold lift
  suffices H : ∀ k j, StrictMono (liftK s k j) from H _ _
  intro k
  induction k with
  | zero => intro j; exact strictMono_id
  | succ k ih =>
    intro j
    have hc : liftK s (k + 1) j = liftK s k (j + 1) ∘ ceilStep s j := funext fun _ => rfl
    rw [hc]
    exact (ih (j + 1)).comp (ceilStep_strictMono (hpos j) (hmono (Nat.le_succ j)))

theorem lift_top {n i : ℕ} (hi : i ≤ n) : lift s n i (s i) = s n := by
  unfold lift
  suffices H : ∀ k j, liftK s k j (s j) = s (j + k) by
    rw [H, Nat.add_sub_cancel' hi]
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ih =>
    intro j
    change liftK s k (j + 1) (ceilStep s j (s j)) = s (j + (k + 1))
    rw [ceilStep_self (hpos j), ih (j + 1), Nat.add_right_comm, Nat.add_assoc]

include hmono in
/-- `π_i` and `π_{i+1}` intertwine the ratio order: `x/s i ≤ y/s(i+1) ↔ π_i x ≤ π_{i+1} y`. -/
theorem lift_le_lift_iff {n i : ℕ} (h : i < n) (x y : ℕ) :
    lift s n i x ≤ lift s n (i + 1) y ↔ x * s (i + 1) ≤ y * s i := by
  rw [lift_succ h, (lift_strictMono hpos hmono n (i + 1)).le_iff_le, ceilStep_le_iff (hpos i)]

end lift

/-! ### The nested sequence of the proof -/

/-- `A_i = π_i(G_i)`, constant from level `n` on. -/
def lhSets (s : ℕ → ℕ) (n i : ℕ) : Finset ℕ :=
  (range (s (min i n) + 1)).image (lift s n (min i n))

/-- `B_i = A_i ∖ {s n}`: the nested sequence of the half-open counts. -/
def lhHalfSets (s : ℕ → ℕ) (n i : ℕ) : Finset ℕ := (lhSets s n i).filter (· < s n)

section sets

variable {s : ℕ → ℕ} (hpos : ∀ i, 0 < s i) (hmono : Monotone s)
include hpos hmono

theorem lhSets_mono (n : ℕ) : Monotone (lhSets s n) := by
  refine monotone_nat_of_le_succ fun i => Finset.le_iff_subset.2 ?_
  rcases le_or_gt n i with hni | hin
  · have h1 : min i n = n := min_eq_right hni
    have h2 : min (i + 1) n = n := min_eq_right (by omega)
    simp only [lhSets, h1, h2, Finset.Subset.refl]
  · have h1 : min i n = i := min_eq_left hin.le
    have h2 : min (i + 1) n = i + 1 := min_eq_left hin
    intro y hy
    simp only [lhSets, h1, h2, Finset.mem_image, Finset.mem_range] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨ceilStep s i x, ?_, (lift_succ hin x).symm⟩
    have hc : ceilStep s i x ≤ s (i + 1) := by
      rw [← ceilStep_self (hpos i)]
      exact (ceilStep_strictMono (hpos i) (hmono (Nat.le_succ i))).monotone (by omega)
    omega

theorem lhHalfSets_mono (n : ℕ) : Monotone (lhHalfSets s n) := by
  intro i j hij
  exact Finset.filter_subset_filter _ (lhSets_mono hpos hmono n hij)

/-- The bijection of the proof of Corollary 6.1, as an identity of endpoint counts. -/
theorem ends_lhSets {n i x : ℕ} (hi : i ≤ n) (hx : x ≤ s i) :
    ends (lhSets s n) i (lift s n i x) = lhEnds s i x := by
  induction i generalizing x with
  | zero =>
    have hmem : lift s n 0 x ∈ lhSets s n 0 := by
      unfold lhSets
      rw [Nat.zero_min]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
    rw [ends, if_pos hmem, lhEnds_zero, if_pos hx]
  | succ i ih =>
    have hin : i < n := by omega
    have hmem : lift s n (i + 1) x ∈ lhSets s n (i + 1) := by
      unfold lhSets
      rw [min_eq_left hi]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
    have hset : lhSets s n i = (range (s i + 1)).image (lift s n i) := by
      unfold lhSets
      rw [min_eq_left hin.le]
    rw [ends, if_pos hmem, lhEnds_succ, if_pos hx, hset, Finset.filter_image,
      Finset.sum_image fun a _ b _ hab => (lift_strictMono hpos hmono n i).injective hab]
    refine Finset.sum_congr
      (Finset.filter_congr fun y _ => lift_le_lift_iff hpos hmono hin y x) fun y hy => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hy
    exact ih hin.le (by omega)

theorem h_lhSets {n d : ℕ} (hd : d ≤ n + 1) : h (lhSets s n) d = lhClosed s d := by
  cases d with
  | zero => rfl
  | succ m =>
    have hset : lhSets s n m = (range (s m + 1)).image (lift s n m) := by
      unfold lhSets
      rw [min_eq_left (by omega)]
    rw [h, lhClosed, hset, Finset.sum_image fun a _ b _ hab =>
      (lift_strictMono hpos hmono n m).injective hab]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_range] at hy
    exact ends_lhSets hpos hmono (by omega) (by omega)

theorem h_lhHalfSets {n d : ℕ} (hd : d ≤ n + 1) : h (lhHalfSets s n) d = lhHalfOpen s d := by
  cases d with
  | zero => rfl
  | succ m =>
    have hset : lhSets s n m = (range (s m + 1)).image (lift s n m) := by
      unfold lhSets
      rw [min_eq_left (by omega)]
    have hends : ∀ v ∈ (lhSets s n m).filter (· < s n),
        ends (lhHalfSets s n) m v = ends (lhSets s n) m v := by
      intro v hv
      have hf := ends_filter (lhSets s n) (· < s n)
        (fun _ _ huv hv' => lt_of_le_of_lt huv hv') m v
      rw [if_pos (Finset.mem_filter.1 hv).2] at hf
      exact hf
    have hfil : (range (s m + 1)).filter (fun x => lift s n m x < s n) = range (s m) := by
      ext x
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range,
        ← lift_top hpos (n := n) (i := m) (by omega),
        (lift_strictMono hpos hmono n m).lt_iff_lt]
      omega
    rw [h, lhHalfOpen]
    change ∑ v ∈ (lhSets s n m).filter (· < s n), ends (lhHalfSets s n) m v = _
    rw [Finset.sum_congr rfl hends, hset, Finset.filter_image, Finset.sum_image fun a _ b _ hab =>
      (lift_strictMono hpos hmono n m).injective hab, hfil]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_range] at hy
    exact ends_lhSets hpos hmono (by omega) (by omega)

/-- **Corollary 6.1 (closed).** For positive nondecreasing `s`, `h_s(D+1) ≥ h_s(D)^⟨D⟩`. -/
theorem lh_reverse_macaulay (D : ℕ) (hD : 1 ≤ D) :
    up D (lhClosed s D) ≤ lhClosed s (D + 1) := by
  rw [← h_lhSets hpos hmono (n := D) (by omega : D ≤ D + 1),
    ← h_lhSets hpos hmono (n := D) (by omega : D + 1 ≤ D + 1)]
  exact nested_reverse_macaulay (lhSets s D) (lhSets_mono hpos hmono D) D hD

/-- **Corollary 6.1 (half-open).** -/
theorem lh_reverse_macaulay_halfOpen (D : ℕ) (hD : 1 ≤ D) :
    up D (lhHalfOpen s D) ≤ lhHalfOpen s (D + 1) := by
  rw [← h_lhHalfSets hpos hmono (n := D) (by omega : D ≤ D + 1),
    ← h_lhHalfSets hpos hmono (n := D) (by omega : D + 1 ≤ D + 1)]
  exact nested_reverse_macaulay (lhHalfSets s D) (lhHalfSets_mono hpos hmono D) D hD

end sets

/-! ### Only the widths `s 0, …, s (D - 1)` enter `h_s(D)` -/

theorem lhEnds_congr {s s' : ℕ → ℕ} {i : ℕ} (h : ∀ j ≤ i, s j = s' j) (x : ℕ) :
    lhEnds s i x = lhEnds s' i x := by
  induction i generalizing x with
  | zero => rw [lhEnds_zero, lhEnds_zero, h 0 le_rfl]
  | succ i ih =>
    have h' : ∀ j ≤ i, s j = s' j := fun j hj => h j (by omega)
    rw [lhEnds_succ, lhEnds_succ, h (i + 1) le_rfl, h i (by omega)]
    simp only [ih h']

theorem lhClosed_congr {s s' : ℕ → ℕ} {d : ℕ} (h : ∀ j < d, s j = s' j) :
    lhClosed s d = lhClosed s' d := by
  cases d with
  | zero => rfl
  | succ m =>
    rw [lhClosed, lhClosed, h m (by omega)]
    exact Finset.sum_congr rfl fun y _ => lhEnds_congr (fun j hj => h j (by omega)) y

theorem lhHalfOpen_congr {s s' : ℕ → ℕ} {d : ℕ} (h : ∀ j < d, s j = s' j) :
    lhHalfOpen s d = lhHalfOpen s' d := by
  cases d with
  | zero => rfl
  | succ m =>
    rw [lhHalfOpen, lhHalfOpen, h m (by omega)]
    exact Finset.sum_congr rfl fun y _ => lhEnds_congr (fun j hj => h j (by omega)) y

/-- **Corollary 6.1** with the paper's hypotheses: only `0 < s_1 ≤ s_2 ≤ ⋯ ≤ s_{D+1}`. -/
theorem lh_reverse_macaulay_of_prefix {s : ℕ → ℕ} {D : ℕ} (hD : 1 ≤ D) (hpos : 0 < s 0)
    (hmono : ∀ i < D, s i ≤ s (i + 1)) : up D (lhClosed s D) ≤ lhClosed s (D + 1) := by
  have hle : ∀ a b, a ≤ b → b ≤ D → s a ≤ s b := by
    intro a b hab hbD
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by omega)).trans (hmono b (by omega))
  have key := lh_reverse_macaulay (s := fun i => s (min i D))
    (fun i => lt_of_lt_of_le hpos (hle 0 _ (Nat.zero_le _) (min_le_right _ _)))
    (fun a b hab => hle _ _ (min_le_min_right D hab) (min_le_right _ _)) D hD
  rwa [lhClosed_congr (s' := s) (d := D) (fun j hj => congrArg s (min_eq_left (by omega))),
    lhClosed_congr (s' := s) (d := D + 1)
      (fun j hj => congrArg s (min_eq_left (by omega)))] at key

theorem lh_reverse_macaulay_halfOpen_of_prefix {s : ℕ → ℕ} {D : ℕ} (hD : 1 ≤ D)
    (hpos : 0 < s 0) (hmono : ∀ i < D, s i ≤ s (i + 1)) :
    up D (lhHalfOpen s D) ≤ lhHalfOpen s (D + 1) := by
  have hle : ∀ a b, a ≤ b → b ≤ D → s a ≤ s b := by
    intro a b hab hbD
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (ih (by omega)).trans (hmono b (by omega))
  have key := lh_reverse_macaulay_halfOpen (s := fun i => s (min i D))
    (fun i => lt_of_lt_of_le hpos (hle 0 _ (Nat.zero_le _) (min_le_right _ _)))
    (fun a b hab => hle _ _ (min_le_min_right D hab) (min_le_right _ _)) D hD
  rwa [lhHalfOpen_congr (s' := s) (d := D) (fun j hj => congrArg s (min_eq_left (by omega))),
    lhHalfOpen_congr (s' := s) (d := D + 1)
      (fun j hj => congrArg s (min_eq_left (by omega)))] at key

/-! ### Small checks -/

example : lhClosed (fun _ => 2) 3 = 10 := by decide
example : lhHalfOpen (fun i => i + 1) 3 = 4 := by decide

end LectureHall
end CbsLean
