import CbsLean.LectureHallMacaulay
import CbsLean.CbLabels

/-!
# Coffee-bean maximality from reverse Macaulay growth (paper §6)

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), Lemma 7.1 and Corollary 7.2, in the conventions of `CbMaximality.lean`
(widths `K = (1, w 0, w 1, …)`, `shell w l` = number of labels of length `l + 2`,
`N_K(n + 1) = 1 + cumShell w n`).

## The bridge

`lastMS w l` is the multiset of last numerators `x_l` of the half-open lecture hall points
`0 ≤ x_0/w_0 ≤ ⋯ ≤ x_l/w_l < 1`.  The room of such a point with respect to the next width is
`chainMap (w l) (w (l+1)) (w l - x_l)` (`card_heads`), so the room multisets of
`CbMaximality.lean` are `rooms w (l + 1) = (lastMS w l).map (room)` (`rooms_succ_eq_map`), and
the counts of `lastMS` are the lecture hall endpoint counts (`count_lastMS`).  Hence
`shell w l = h°_w(l + 1)` and `1 + cumShell w d = h_w(d)` (Lemma 7.1 with `k₁ = 1`).

A finite width vector `K = (1, k₂, …, k_L)` is handled by repeating its last width: the counts
up to level `L` depend only on `w 0, …, w (L - 2)` (`one_add_cumShell`, `lhClosed_congr`).

## Main results

| paper | Lean |
|---|---|
| Lemma 7.1, clause `k₁ = 1` | `one_add_cumShell`, `shell_eq_lhHalfOpen` |
| `N_{cb(k)}(d + 1) = C(k + d, d)` | `one_add_cumShellCb` |
| Corollary 7.2 (1) | `cumulative_reverse_macaulay` |
| Corollary 7.2 (2), single crossing | `single_crossing` |
| Corollary 7.2 (3), cb maximality (second proof) | `cb_maximality_macaulay` |
| shell form (half-open, Corollary 6.1) | `shell_reverse_macaulay`, `claimS_macaulay` |

`cb_maximality_macaulay` has exactly the statement of `CbMax.cb_maximality`; its proof does not
use the effective width `kappa`, the shift predicates or Claim K.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

open Macaulay LectureHall

/-- Last numerators of the half-open lecture hall points with widths `(w 0, …, w l)`. -/
def lastMS (w : ℕ → ℕ) : ℕ → Multiset ℕ
  | 0 => Multiset.range (w 0)
  | l + 1 => (lastMS w l).bind (fun x => (heads x (w l) (w (l + 1))).val)

theorem lt_of_mem_lastMS (w : ℕ → ℕ) (l : ℕ) {x : ℕ} (hx : x ∈ lastMS w l) : x < w l := by
  cases l with
  | zero => exact Multiset.mem_range.mp hx
  | succ l =>
    simp only [lastMS, Multiset.mem_bind, Finset.mem_val, heads, Finset.mem_filter,
      Finset.mem_range] at hx
    obtain ⟨_, _, h, _⟩ := hx
    exact h

/-- The rooms of `CbMaximality.lean` are the rooms of the half-open points. -/
theorem rooms_succ_eq_map (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (l : ℕ) :
    rooms w (l + 1) = (lastMS w l).map (fun x => chainMap (w l) (w (l + 1)) (w l - x)) := by
  induction l with
  | zero =>
    have h := heads_val_map_reflect 0 1 (w 0) (w 1) Nat.one_pos Nat.one_pos
    have hh : heads 0 1 (w 0) = Finset.range (w 0) := by
      unfold heads
      exact Finset.filter_true_of_mem (fun x _ => by simp)
    have hc : chainMap 1 (w 0) (1 - 0) = w 0 := by simp [chainMap]
    rw [hh, Finset.range_val, hc] at h
    simp only [rooms, Phi, Multiset.singleton_bind, lastMS]
    exact h.symm
  | succ l ih =>
    rw [rooms, ih, Phi, Multiset.bind_map, lastMS, Multiset.map_bind]
    apply Multiset.bind_congr
    intro x hx
    exact (heads_val_map_reflect x (w l) (w (l + 1)) (w (l + 1 + 1)) (hpos l)
      (lt_of_mem_lastMS w l hx)).symm

theorem shell_eq_card_lastMS (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (l : ℕ) :
    shell w l = Multiset.card (lastMS w l) := by
  cases l with
  | zero => simp [shell, rooms, lastMS]
  | succ l =>
    rw [shell, rooms_succ_eq_map w hpos l, lastMS, Multiset.card_bind]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    rw [Function.comp_apply, Finset.card_val,
      card_heads x (w l) (w (l + 1)) (hpos l) (lt_of_mem_lastMS w l hx)]

theorem count_lastMS (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (l y : ℕ) :
    (lastMS w l).count y = if y < w l then lhEnds w l y else 0 := by
  induction l generalizing y with
  | zero =>
    rw [lastMS, Multiset.count_eq_of_nodup (Multiset.nodup_range _), lhEnds_zero]
    by_cases hy : y < w 0
    · rw [if_pos (Multiset.mem_range.2 hy), if_pos hy, if_pos hy.le]
    · rw [if_neg (fun h => hy (Multiset.mem_range.1 h)), if_neg hy]
  | succ l ih =>
    have hsupp : (lastMS w l).toFinset ⊆ range (w l) := fun x hx =>
      mem_range.2 (lt_of_mem_lastMS w l (Multiset.mem_toFinset.1 hx))
    rw [lastMS, Multiset.count_bind, Finset.sum_multiset_map_count]
    rw [Finset.sum_subset hsupp (fun x _ hx => by
      rw [Multiset.count_eq_zero.2 (fun h => hx (Multiset.mem_toFinset.2 h)), zero_smul])]
    have hterm : ∀ x ∈ range (w l), (lastMS w l).count x •
        (heads x (w l) (w (l + 1))).val.count y =
        if x * w (l + 1) ≤ y * w l ∧ y < w (l + 1) then lhEnds w l x else 0 := by
      intro x hx
      rw [ih, if_pos (mem_range.1 hx), Multiset.count_eq_of_nodup (Finset.nodup _), smul_eq_mul]
      have hmem : y ∈ (heads x (w l) (w (l + 1))).val ↔
          x * w (l + 1) ≤ y * w l ∧ y < w (l + 1) := by
        rw [Finset.mem_val, heads, Finset.mem_filter, mem_range, and_comm]
      by_cases hc : x * w (l + 1) ≤ y * w l ∧ y < w (l + 1)
      · rw [if_pos (hmem.2 hc), if_pos hc, mul_one]
      · rw [if_neg (fun h => hc (hmem.1 h)), if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hy : y < w (l + 1)
    · rw [if_pos hy, lhEnds_succ, if_pos hy.le, Finset.sum_filter, Finset.sum_range_succ]
      have hlast : ¬ w l * w (l + 1) ≤ y * w l := by
        intro h
        rw [mul_comm (w l)] at h
        exact absurd (Nat.le_of_mul_le_mul_right h (hpos l)) (Nat.not_le.2 hy)
      rw [if_neg hlast, add_zero]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hc : x * w (l + 1) ≤ y * w l
      · rw [if_pos ⟨hc, hy⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.1), if_neg hc]
    · rw [if_neg hy]
      exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hy h.2))

/-- Half-open form behind Lemma 7.1: `g_{l+2}(K) = h°_{(w 0, …, w l)}(l + 1)`. -/
theorem shell_eq_lhHalfOpen (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (l : ℕ) :
    shell w l = lhHalfOpen w (l + 1) := by
  rw [shell_eq_card_lastMS w hpos l, ← Multiset.sum_count_eq_card (s := range (w l))
    (fun a ha => mem_range.2 (lt_of_mem_lastMS w l ha)), lhHalfOpen]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [count_lastMS w hpos, if_pos (mem_range.1 hy)]

/-- **Lemma 7.1** (`k₁ = 1`). `N_K(d + 1) = 1 + cumShell w d = h_{(w 0, …, w (d-1))}(d)`. -/
theorem one_add_cumShell (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (d : ℕ) :
    1 + cumShell w d = lhClosed w d := by
  induction d with
  | zero => simp [cumShell, lhClosed]
  | succ d ih =>
    unfold cumShell at ih ⊢
    rw [Finset.sum_range_succ, lhClosed_succ, shell_eq_lhHalfOpen w hpos d]
    omega

/-- `N_{cb(k)}(d + 1) = C(k + d, d)`. -/
theorem one_add_cumShellCb (k d : ℕ) : 1 + cumShellCb k d = Nat.choose (k + d) d := by
  induction d with
  | zero => simp [cumShellCb]
  | succ d ih =>
    unfold cumShellCb at ih ⊢
    rw [Finset.sum_range_succ, ← add_assoc, ih, ← add_assoc, Nat.choose_succ_succ', shellCb]

/-- Reverse Macaulay growth of the shells (half-open lecture hall counts). -/
theorem shell_reverse_macaulay (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w)
    (l : ℕ) : up (l + 1) (shell w l) ≤ shell w (l + 1) := by
  rw [shell_eq_lhHalfOpen w hpos l, shell_eq_lhHalfOpen w hpos (l + 1)]
  exact lh_reverse_macaulay_halfOpen hpos hmono (l + 1) (by omega)

/-- The cb shells grow at exactly Macaulay's rate. -/
theorem shellCb_up (i k : ℕ) : up (i + 1) (shellCb i k) = shellCb (i + 1) k := by
  unfold shellCb
  rw [up_choose (by omega : 1 ≤ i + 1) (k + i), (by omega : k + (i + 1) = k + i + 1)]

/-- **Claim S** from reverse Macaulay growth (no effective width needed). -/
theorem claimS_macaulay (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k i : ℕ)
    (h : shellCb i k ≤ shell w i) : shellCb (i + 1) k ≤ shell w (i + 1) := by
  rw [← shellCb_up]
  exact le_trans (up_mono _ h) (shell_reverse_macaulay w hpos hmono i)

/-- **Corollary 7.2 (1).** `H(d + 1) ≥ H(d)^⟨d⟩` for `H(d) = N_K(d + 1)`, `d ≥ 1`. -/
theorem cumulative_reverse_macaulay (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w)
    (d : ℕ) (hd : 1 ≤ d) : up d (1 + cumShell w d) ≤ 1 + cumShell w (d + 1) := by
  rw [one_add_cumShell w hpos d, one_add_cumShell w hpos (d + 1)]
  exact lh_reverse_macaulay hpos hmono d hd

/-- **Corollary 7.2 (2), single crossing.** If `M` has maximal Macaulay growth from `d₀ ≥ 1` on
and `H(d₁) > M(d₁)` for some `d₁ ≥ d₀`, then `H(d) > M(d)` for every `d ≥ d₁`. -/
theorem single_crossing (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (M : ℕ → ℕ)
    (d₀ : ℕ) (hd₀ : 1 ≤ d₀) (hM : ∀ d, d₀ ≤ d → M (d + 1) = up d (M d)) (d₁ : ℕ)
    (hd₁ : d₀ ≤ d₁) (h : M d₁ < 1 + cumShell w d₁) :
    ∀ d, d₁ ≤ d → M d < 1 + cumShell w d := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact h
  | succ d hd ih =>
    rw [hM d (by omega)]
    calc up d (M d) < up d (1 + cumShell w d) := up_strictMono (by omega) ih
      _ ≤ 1 + cumShell w (d + 1) := cumulative_reverse_macaulay w hpos hmono d (by omega)

/-- **Corollary 7.2 (3), cb maximality** (second proof of `cb_maximality`, for all `k` at
once). -/
theorem cb_maximality_macaulay (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w)
    (k L : ℕ) (hL : cumShell w L ≤ cumShellCb k L) :
    ∀ n, n ≤ L → cumShell w n ≤ cumShellCb k n := by
  intro n hn
  by_contra hcon
  push_neg at hcon
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp [cumShell, cumShellCb] at hcon
    · exact h0
  have hM : ∀ d, 1 ≤ d → 1 + cumShellCb k (d + 1) = up d (1 + cumShellCb k d) := by
    intro d hd
    rw [one_add_cumShellCb, one_add_cumShellCb, up_choose hd, Nat.add_assoc]
  have hcross := single_crossing w hpos hmono (fun d => 1 + cumShellCb k d) 1 le_rfl hM n hn1
    (by dsimp only; omega) L hn
  dsimp only at hcross
  omega

/-! ### Small checks -/

example : shell (fun i => i + 2) 2 = lhHalfOpen (fun i => i + 2) 3 := by decide

end CbMax
end CbsLean
