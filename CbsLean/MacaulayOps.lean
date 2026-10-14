import Mathlib

/-!
# Macaulay representations and the operators `x^⟨D⟩`, `x_⟨D⟩`, `S_D`

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), §2.

## Conventions

* Every `x ≥ 0` has a unique `D`-th Macaulay representation
  `x = C(a_D, D) + C(a_{D-1}, D-1) + ⋯ + C(a_t, t)` with `a_D > ⋯ > a_t ≥ t ≥ 1`.
  We never build the list `(a_j)`: `top D x` is the greedy top coefficient `a_D`, and the
  operators are defined by peeling off the top term and recursing on `D - 1`.
* `up D x = x^⟨D⟩` (Macaulay), `low D x = x_⟨D⟩` (Green's lower operator),
  `S D x = x - x_⟨D⟩`, `kk D x = x^{(D)}` (Kruskal–Katona).  All four vanish at `x = 0`;
  `up`, `low` and `kk` also vanish at `D = 0`, while `S 0 x = x` (the paper uses `D ≥ 1`).

## Correspondence with the paper (Lemma 2.1)

| paper | Lean |
|---|---|
| uniqueness of the top term | `top_spec`, `top_eq_of`, `top_split` |
| (a), one term at a time | `S_split`, `S_iterate_split` |
| (b) | `low_succ_le`, `low_le_succ`, `low_mono`, `S_mono` |
| (c) | `low_up` (stated for `D + 1`) |
| (d) | `up_eq_add_up_S` (one-step form (d′)), `up_eq_sum_iterate` (summed form) |
| (e) | `up_strictMono` |
| `x^{(D)} = x^⟨D⟩ - x` | `kk_add_self` |
| `C(n + D, D)^⟨D⟩ = C(n + D + 1, D + 1)` | `up_choose` |
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace Macaulay

/-- Top coefficient of the `D`-th Macaulay representation of `x`: the greatest `a ≤ x + D`
with `C(a, D) ≤ x` (for `1 ≤ D` and `0 < x`). -/
def top (D x : ℕ) : ℕ := Nat.findGreatest (fun a => Nat.choose a D ≤ x) (x + D)

/-- Macaulay's upper operator `x^⟨D⟩ = ∑ C(a_j + 1, j + 1)`. -/
def up : ℕ → ℕ → ℕ
  | 0, _ => 0
  | D + 1, x =>
      if x = 0 then 0
      else Nat.choose (top (D + 1) x + 1) (D + 2) +
        up D (x - Nat.choose (top (D + 1) x) (D + 1))

/-- Green's lower operator `x_⟨D⟩ = ∑ C(a_j - 1, j - 1)`. -/
def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | D + 1, x =>
      if x = 0 then 0
      else Nat.choose (top (D + 1) x - 1) D +
        low D (x - Nat.choose (top (D + 1) x) (D + 1))

/-- `S_D(x) = x - x_⟨D⟩ = ∑ C(a_j - 1, j)`. -/
def S (D x : ℕ) : ℕ := x - low D x

/-- Kruskal–Katona upper operator `x^{(D)} = ∑ C(a_j, j + 1)`. -/
def kk : ℕ → ℕ → ℕ
  | 0, _ => 0
  | D + 1, x =>
      if x = 0 then 0
      else Nat.choose (top (D + 1) x) (D + 2) +
        kk D (x - Nat.choose (top (D + 1) x) (D + 1))

/-! ### The top coefficient -/

theorem lt_choose_add (D x : ℕ) (hD : 1 ≤ D) : x < Nat.choose (x + D) D := by
  induction D, hD using Nat.le_induction with
  | base =>
    rw [Nat.choose_one_right]
    omega
  | succ n _ ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ']
    omega

theorem top_spec {D x : ℕ} (hD : 1 ≤ D) (hx : 0 < x) :
    Nat.choose (top D x) D ≤ x ∧ x < Nat.choose (top D x + 1) D := by
  have h0 : Nat.choose 0 D ≤ x := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    omega
  refine ⟨Nat.findGreatest_spec (P := fun a => Nat.choose a D ≤ x) (Nat.zero_le _) h0, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hle : top D x + 1 ≤ x + D := by
    by_contra h'
    have h1 : Nat.choose (x + D) D ≤ Nat.choose (top D x + 1) D :=
      Nat.choose_le_choose D (by omega)
    have h2 := lt_choose_add D x hD
    omega
  have h3 : top D x + 1 ≤ top D x :=
    Nat.le_findGreatest (P := fun a => Nat.choose a D ≤ x) hle hcon
  omega

theorem top_eq_of {D x a : ℕ} (hD : 1 ≤ D) (h1 : Nat.choose a D ≤ x)
    (h2 : x < Nat.choose (a + 1) D) : top D x = a := by
  have hlt := lt_choose_add D x hD
  have ha : a ≤ x + D := by
    by_contra h'
    have : Nat.choose (x + D) D ≤ Nat.choose a D := Nat.choose_le_choose D (by omega)
    omega
  unfold top
  rw [Nat.findGreatest_eq_iff]
  refine ⟨ha, fun _ => h1, fun n hn _ hn' => ?_⟩
  have : Nat.choose (a + 1) D ≤ Nat.choose n D := Nat.choose_le_choose D hn
  omega

theorem le_top {D x : ℕ} (hD : 1 ≤ D) (hx : 0 < x) : D ≤ top D x := by
  have h := (top_spec hD hx).2
  by_contra hlt
  have h1 : Nat.choose (top D x + 1) D ≤ Nat.choose D D := Nat.choose_le_choose D (by omega)
  rw [Nat.choose_self] at h1
  omega

/-- The top term of `C(a, D + 1) + r` with `r < C(a, D)` is `C(a, D + 1)`. -/
theorem top_split {D a r : ℕ} (h : r < Nat.choose a D) :
    top (D + 1) (Nat.choose a (D + 1) + r) = a := by
  refine top_eq_of (by omega) (by omega) ?_
  rw [Nat.choose_succ_succ']
  omega

/-- Every `x > 0` splits as `C(a, D + 1) + r` with `r < C(a, D)` and `D + 1 ≤ a`. -/
theorem exists_split (D : ℕ) {x : ℕ} (hx : 0 < x) :
    ∃ a r, x = Nat.choose a (D + 1) + r ∧ r < Nat.choose a D ∧ D + 1 ≤ a := by
  obtain ⟨h1, h2⟩ := top_spec (D := D + 1) (by omega) hx
  have h3 := le_top (D := D + 1) (by omega) hx
  rw [Nat.choose_succ_succ'] at h2
  exact ⟨top (D + 1) x, x - Nat.choose (top (D + 1) x) (D + 1), by omega, by omega, h3⟩

/-! ### Values at `0` and in degree `1` -/

@[simp] theorem up_zero_right (D : ℕ) : up D 0 = 0 := by
  cases D <;> simp [up]

@[simp] theorem low_zero_right (D : ℕ) : low D 0 = 0 := by
  cases D <;> simp [low]

@[simp] theorem S_zero_right (D : ℕ) : S D 0 = 0 := by
  simp [S]

@[simp] theorem kk_zero_right (D : ℕ) : kk D 0 = 0 := by
  cases D <;> simp [kk]

theorem up_one (x : ℕ) : up 1 x = Nat.choose (x + 1) 2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have ht : top 1 x = x := top_eq_of le_rfl (by simp) (by simp)
    rw [up, if_neg (by omega), ht]
    simp [up]

theorem low_one (x : ℕ) : low 1 x = if x = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have ht : top 1 x = x := top_eq_of le_rfl (by simp) (by simp)
    rw [low, if_neg (by omega), if_neg (by omega), ht]
    simp [low]

/-! ### Splitting off the top term -/

theorem up_split {D a r : ℕ} (h : r < Nat.choose a D) :
    up (D + 1) (Nat.choose a (D + 1) + r) = Nat.choose (a + 1) (D + 2) + up D r := by
  by_cases hx : Nat.choose a (D + 1) + r = 0
  · have hr : r = 0 := by omega
    have hc : Nat.choose a (D + 1) = 0 := by omega
    have ha1 : a < D + 1 := Nat.choose_eq_zero_iff.mp hc
    have ha2 : D ≤ a := by
      by_contra hlt
      rw [Nat.choose_eq_zero_of_lt (by omega)] at h
      omega
    have had : a = D := by omega
    subst hr had
    rw [hc, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · rw [up, if_neg hx, top_split h, Nat.add_sub_cancel_left]

theorem low_split {D a r : ℕ} (h : r < Nat.choose a D) (ha : D + 1 ≤ a) :
    low (D + 1) (Nat.choose a (D + 1) + r) = Nat.choose (a - 1) D + low D r := by
  have hpos : 0 < Nat.choose a (D + 1) := Nat.choose_pos ha
  rw [low, if_neg (by omega), top_split h, Nat.add_sub_cancel_left]

theorem kk_split {D a r : ℕ} (h : r < Nat.choose a D) :
    kk (D + 1) (Nat.choose a (D + 1) + r) = Nat.choose a (D + 2) + kk D r := by
  by_cases hx : Nat.choose a (D + 1) + r = 0
  · have hr : r = 0 := by omega
    have hc : Nat.choose a (D + 1) = 0 := by omega
    have ha1 : a < D + 1 := Nat.choose_eq_zero_iff.mp hc
    rw [hx, hr, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · rw [kk, if_neg hx, top_split h, Nat.add_sub_cancel_left]

theorem low_le_self_aux {D a : ℕ} (ha : 1 ≤ a) :
    Nat.choose a (D + 1) = Nat.choose (a - 1) D + Nat.choose (a - 1) (D + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact Nat.choose_succ_succ' b D

theorem low_le_self (D x : ℕ) : low D x ≤ x := by
  induction D generalizing x with
  | zero => simp [low]
  | succ D ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    obtain ⟨a, r, rfl, hr, ha⟩ := exists_split D hx
    rw [low_split hr ha]
    have h1 := ih r
    have h2 := low_le_self_aux (D := D) (a := a) (by omega)
    omega

theorem S_split {D a r : ℕ} (h : r < Nat.choose a D) (ha : D + 1 ≤ a) :
    S (D + 1) (Nat.choose a (D + 1) + r) = Nat.choose (a - 1) (D + 1) + S D r := by
  simp only [S]
  rw [low_split h ha]
  have h1 := low_le_self D r
  have h2 := low_le_self_aux (D := D) (a := a) (by omega)
  omega

theorem S_le_self (D x : ℕ) : S D x ≤ x := Nat.sub_le x (low D x)

theorem low_pos {D x : ℕ} (hD : 1 ≤ D) (hx : 0 < x) : 0 < low D x := by
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
  obtain ⟨a, r, rfl, hr, ha⟩ := exists_split E hx
  rw [low_split hr ha]
  have h1 := Nat.choose_pos (by omega : E ≤ a - 1)
  omega

theorem S_lt_self {D x : ℕ} (hD : 1 ≤ D) (hx : 0 < x) : S D x < x := by
  have h1 := low_pos hD hx
  have h2 := low_le_self D x
  simp only [S]
  omega

/-- `S_D` maps the band below `C(a, D)` into the band below `C(a - 1, D)`. -/
theorem S_lt_band {D a r : ℕ} (ha : D < a) (h : r < Nat.choose a D) :
    S D r < Nat.choose (a - 1) D := by
  induction D generalizing a r with
  | zero =>
    rw [Nat.choose_zero_right] at h ⊢
    simp only [S, low]
    omega
  | succ D ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [S_zero_right]
      exact Nat.choose_pos (by omega)
    obtain ⟨b, r', rfl, hr', hb⟩ := exists_split D hr
    rw [S_split hr' hb]
    have h1 := ih (a := b) (r := r') (by omega) hr'
    have hba : b < a := by
      by_contra hab
      have h3 := Nat.choose_le_choose (D + 1) (Nat.le_of_not_lt hab)
      omega
    have h4 := Nat.choose_le_choose (D + 1) (by omega : b ≤ a - 1)
    have h5 := low_le_self_aux (D := D) (a := b) (by omega)
    omega

/-! ### Lemma 2.1 (e) and binomial values -/

theorem up_choose {D : ℕ} (hD : 1 ≤ D) (a : ℕ) :
    up D (Nat.choose a D) = Nat.choose (a + 1) (D + 1) := by
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
  rcases Nat.lt_or_ge a E with ha | ha
  · rw [Nat.choose_eq_zero_of_lt (by omega : a < E + 1),
      Nat.choose_eq_zero_of_lt (by omega : a + 1 < E + 1 + 1), up_zero_right]
  · have h := up_split (D := E) (a := a) (r := 0) (Nat.choose_pos ha)
    rw [Nat.add_zero, up_zero_right, Nat.add_zero] at h
    exact h

theorem up_strictMono_aux : StrictMono fun n => Nat.choose (n + 1) 2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h : Nat.choose (n + 1 + 1) 2 = Nat.choose (n + 1) 1 + Nat.choose (n + 1) 2 :=
    Nat.choose_succ_succ' (n + 1) 1
  rw [Nat.choose_one_right] at h
  change Nat.choose (n + 1) 2 < Nat.choose (n + 1 + 1) 2
  omega

/-- **Lemma 2.1 (e).** `x ↦ x^⟨D⟩` is strictly increasing for `D ≥ 1`. -/
theorem up_strictMono {D : ℕ} (hD : 1 ≤ D) : StrictMono (up D) := by
  induction D, hD using Nat.le_induction with
  | base =>
    intro u v huv
    rw [up_one, up_one]
    exact up_strictMono_aux huv
  | succ D hD ih =>
    intro u v huv
    obtain ⟨b, s, rfl, hs, hb⟩ := exists_split D (by omega : 0 < v)
    rw [up_split hs]
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · have hpos : 0 < Nat.choose (b + 1) (D + 2) := Nat.choose_pos (by omega)
      rw [up_zero_right]
      omega
    obtain ⟨a, r, rfl, hr, ha⟩ := exists_split D hu
    rw [up_split hr]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h1 : up D r < up D (Nat.choose a D) := ih hr
      rw [up_choose hD] at h1
      have h2 : Nat.choose (a + 2) (D + 2) =
          Nat.choose (a + 1) (D + 1) + Nat.choose (a + 1) (D + 2) :=
        Nat.choose_succ_succ' (a + 1) (D + 1)
      have h3 : Nat.choose (a + 2) (D + 2) ≤ Nat.choose (b + 1) (D + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega
    · have h1 : up D r < up D s := ih (by omega)
      omega
    · have h1 : Nat.choose (b + 1) (D + 1) = Nat.choose b D + Nat.choose b (D + 1) :=
        Nat.choose_succ_succ' b D
      have h2 : Nat.choose (b + 1) (D + 1) ≤ Nat.choose a (D + 1) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem up_mono (D : ℕ) : Monotone (up D) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · intro u v _
    simp only [up, le_refl]
  · exact (up_strictMono hD).monotone

/-! ### Lemma 2.1 (d) -/

/-- **Lemma 2.1 (d′).** `x^⟨D⟩ = x + S_D(x)^⟨D⟩`. -/
theorem up_eq_add_up_S {D : ℕ} (hD : 1 ≤ D) (x : ℕ) : up D x = x + up D (S D x) := by
  induction D, hD using Nat.le_induction generalizing x with
  | base =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      have hS : S 1 (y + 1) = y := by
        simp only [S, low_one, if_neg (Nat.succ_ne_zero y)]
        omega
      have hP := Nat.choose_succ_succ' (y + 1) 1
      rw [Nat.choose_one_right] at hP
      rw [hS, up_one, up_one]
      exact hP
  | succ D hD ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · obtain ⟨a, r, rfl, hr, ha⟩ := exists_split D hx
      have hb := S_lt_band (by omega : D < a) hr
      have ha1 : a - 1 + 1 = a := by omega
      have hP : Nat.choose (a + 1) (D + 2) = Nat.choose a (D + 1) + Nat.choose a (D + 2) :=
        Nat.choose_succ_succ' a (D + 1)
      rw [up_split hr, S_split hr ha, up_split hb, ha1, ih r, hP]
      omega

theorem le_up {D : ℕ} (hD : 1 ≤ D) (x : ℕ) : x ≤ up D x := by
  rw [up_eq_add_up_S hD x]
  omega

theorem up_eq_sum_iterate_aux {D : ℕ} (hD : 1 ≤ D) (x n : ℕ) :
    up D x = ∑ r ∈ range n, (S D)^[r] x + up D ((S D)^[n] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := up_eq_add_up_S hD ((S D)^[n] x)
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    omega

theorem up_eq_sum_iterate_aux2 {D : ℕ} (hD : 1 ≤ D) (x n : ℕ) : (S D)^[n] x ≤ x - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases Nat.eq_zero_or_pos ((S D)^[n] x) with h | h
    · rw [h, S_zero_right]
      omega
    · have := S_lt_self hD h
      omega

/-- **Lemma 2.1 (d).** `x^⟨D⟩ = ∑_{r ≥ 0} S_D^r(x)` (the sum is finite: `S_D^r(x) = 0` for
`r > x`). -/
theorem up_eq_sum_iterate {D : ℕ} (hD : 1 ≤ D) (x : ℕ) :
    up D x = ∑ r ∈ range (x + 1), (S D)^[r] x := by
  have h := up_eq_sum_iterate_aux2 hD x (x + 1)
  have h0 : (S D)^[x + 1] x = 0 := by omega
  rw [up_eq_sum_iterate_aux hD x (x + 1), h0, up_zero_right, Nat.add_zero]

theorem S_iterate_split_aux {D a y : ℕ} (h : y < Nat.choose a D) (r : ℕ) :
    (S D)^[r] y < Nat.choose (a - r) D ∨ (S D)^[r] y = 0 := by
  induction r with
  | zero => exact Or.inl (by simpa using h)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h1 | h1
    · by_cases hD : D < a - n
      · left
        have e : a - (n + 1) = a - n - 1 := by omega
        rw [e]
        exact S_lt_band hD h1
      · right
        have hc : Nat.choose (a - n) D ≤ 1 := by
          rcases Nat.lt_or_ge (a - n) D with h2 | h2
          · rw [Nat.choose_eq_zero_of_lt h2]
            omega
          · have e : a - n = D := by omega
            rw [e, Nat.choose_self]
        have h0 : (S D)^[n] y = 0 := by omega
        rw [h0]
        exact S_zero_right D
    · right
      rw [h1]
      exact S_zero_right D

/-- **Lemma 2.1 (a)**, one term at a time: `S_{D+1}^r (C(a, D+1) + y) = C(a - r, D+1) + S_D^r y`
when `y < C(a, D)`. -/
theorem S_iterate_split {D a y : ℕ} (h : y < Nat.choose a D) (r : ℕ) :
    (S (D + 1))^[r] (Nat.choose a (D + 1) + y) = Nat.choose (a - r) (D + 1) + (S D)^[r] y := by
  induction r with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih]
    have hinv := S_iterate_split_aux h n
    have e : a - (n + 1) = a - n - 1 := by omega
    rw [e]
    by_cases hD : D + 1 ≤ a - n
    · have hy : (S D)^[n] y < Nat.choose (a - n) D := by
        rcases hinv with h1 | h1
        · exact h1
        · rw [h1]
          exact Nat.choose_pos (by omega)
      exact S_split hy hD
    · have hy : (S D)^[n] y = 0 := by
        rcases hinv with h1 | h1
        · have hc : Nat.choose (a - n) D ≤ 1 := by
            rcases Nat.lt_or_ge (a - n) D with h2 | h2
            · rw [Nat.choose_eq_zero_of_lt h2]
              omega
            · have e2 : a - n = D := by omega
              rw [e2, Nat.choose_self]
          omega
        · exact h1
      rw [hy, Nat.choose_eq_zero_of_lt (by omega : a - n < D + 1),
        Nat.choose_eq_zero_of_lt (by omega : a - n - 1 < D + 1)]
      simp

/-- `x^{(D)} + x = x^⟨D⟩`. -/
theorem kk_add_self {D : ℕ} (hD : 1 ≤ D) (x : ℕ) : kk D x + x = up D x := by
  induction D, hD using Nat.le_induction generalizing x with
  | base =>
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      simp
    · obtain ⟨a, r, rfl, hr, -⟩ := exists_split 0 hx
      have hr0 : r = 0 := by
        rw [Nat.choose_zero_right] at hr
        omega
      subst hr0
      rw [kk_split hr, up_split hr]
      have hp : Nat.choose (a + 1) (0 + 2) = Nat.choose a 1 + Nat.choose a 2 :=
        Nat.choose_succ_succ' a 1
      simp only [kk_zero_right, up_zero_right, Nat.zero_add] at hp ⊢
      omega
  | succ D _ ih =>
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      simp
    · obtain ⟨a, r, rfl, hr, -⟩ := exists_split D hx
      rw [kk_split hr, up_split hr]
      have hp : Nat.choose (a + 1) (D + 2) = Nat.choose a (D + 1) + Nat.choose a (D + 2) :=
        Nat.choose_succ_succ' a (D + 1)
      have := ih r
      omega

/-! ### Lemma 2.1 (b) -/

/-- The identity `(C(a, E) - 1)_⟨E⟩ = C(a - 1, E - 1)` for `a ≥ E + 1`. -/
theorem low_choose_sub_one {E a : ℕ} (hE : 1 ≤ E) (ha : E + 1 ≤ a) :
    low E (Nat.choose a E - 1) = Nat.choose (a - 1) (E - 1) := by
  induction E, hE using Nat.le_induction generalizing a with
  | base =>
    have h0 : a - 1 ≠ 0 := by omega
    rw [Nat.choose_one_right, low_one, if_neg h0]
    simp
  | succ E hE ih =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hpos : 0 < Nat.choose b E := Nat.choose_pos (by omega)
    have h1 : Nat.choose (b + 1) (E + 1) - 1 =
        Nat.choose b (E + 1) + (Nat.choose b E - 1) := by
      rw [Nat.choose_succ_succ' b E]; omega
    have h2 : Nat.choose b E - 1 < Nat.choose b E := by omega
    rw [h1, low_split h2 (by omega), ih (a := b) (by omega)]
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    obtain ⟨F, rfl⟩ : ∃ F, E = F + 1 := ⟨E - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.choose_succ_succ' c F]
    omega

theorem low_succ_le_aux (D x : ℕ) :
    low D x ≤ low D (x + 1) ∧ low D (x + 1) ≤ low D x + 1 := by
  induction D generalizing x with
  | zero => simp [low]
  | succ D ih =>
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · rw [Nat.zero_add, low_one, low_one]
      by_cases hx : x = 0 <;> simp [hx]
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · have h1 : low (D + 1) 1 = 1 := by
        have := low_split (D := D) (a := D + 1) (r := 0) (Nat.choose_pos (by omega)) le_rfl
        simpa using this
      rw [low_zero_right, Nat.zero_add, h1]
      omega
    obtain ⟨a, r, rfl, hr, ha⟩ := exists_split D hx
    rcases Nat.lt_or_ge (r + 1) (Nat.choose a D) with h | h
    · rw [Nat.add_assoc, low_split hr ha, low_split h ha]
      have := ih r
      omega
    · have hreq : r + 1 = Nat.choose a D := by omega
      have e1 : Nat.choose a (D + 1) + r + 1 = Nat.choose (a + 1) (D + 1) + 0 := by
        rw [Nat.choose_succ_succ' a D]; omega
      have hp : 0 < Nat.choose (a + 1) D := Nat.choose_pos (by omega)
      rw [e1, low_split hp (by omega), low_split hr ha, low_zero_right]
      have hr' : r = Nat.choose a D - 1 := by omega
      rw [hr', low_choose_sub_one hD ha]
      have hp2 : Nat.choose (a - 1) D + Nat.choose (a - 1) (D - 1) = Nat.choose a D := by
        obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
        obtain ⟨F, rfl⟩ : ∃ F, D = F + 1 := ⟨D - 1, by omega⟩
        rw [Nat.choose_succ_succ' c F]
        simp only [Nat.add_sub_cancel]
        omega
      simp only [Nat.add_sub_cancel]
      omega

theorem low_succ_le (D x : ℕ) : low D (x + 1) ≤ low D x + 1 := by
  exact (low_succ_le_aux D x).2

theorem low_le_succ (D x : ℕ) : low D x ≤ low D (x + 1) := by
  exact (low_succ_le_aux D x).1

/-- **Lemma 2.1 (b).** `x ↦ x_⟨D⟩` is nondecreasing. -/
theorem low_mono (D : ℕ) : Monotone (low D) := by
  exact monotone_nat_of_le_succ (low_le_succ D)

/-- **Lemma 2.1 (b).** `S_D` is nondecreasing. -/
theorem S_mono (D : ℕ) : Monotone (S D) := by
  refine monotone_nat_of_le_succ fun x => ?_
  have h1 := low_succ_le D x
  have h2 := low_le_self D x
  simp only [S]
  omega

/-! ### Lemma 2.1 (c) -/

/-- **Lemma 2.1 (c).** `(y^⟨D⟩)_⟨D+1⟩ = y` for `D ≥ 1`. -/
theorem low_up {D : ℕ} (hD : 1 ≤ D) (y : ℕ) : low (D + 1) (up D y) = y := by
  induction D, hD using Nat.le_induction generalizing y with
  | base =>
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp
    · have h0 : (0 : ℕ) < Nat.choose (y + 1) 1 := by simp
      have h2 := low_split h0 (by omega : 1 + 1 ≤ y + 1)
      rw [up_one]
      simpa using h2
  | succ D hD ih =>
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp
    · obtain ⟨b, r, rfl, hr, hb⟩ := exists_split D hy
      have hlt : up D r < Nat.choose (b + 1) (D + 1) := by
        rw [← up_choose hD b]
        exact up_strictMono hD hr
      have h2 : low (D + 1 + 1) (Nat.choose (b + 1) (D + 2) + up D r) =
          Nat.choose b (D + 1) + r := by
        have h3 := low_split hlt (by omega : D + 1 + 1 ≤ b + 1)
        rw [ih] at h3
        simpa using h3
      rw [up_split hr, h2]

/-! ### Small checks -/

example : up 2 4 = 5 := by decide
example : low 2 7 = 4 := by decide
example : S 3 10 = 4 := by decide
example : kk 2 6 = 4 := by decide

end Macaulay
end CbsLean
