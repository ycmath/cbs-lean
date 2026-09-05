import CbsLean.CbMaximality

/-!
# Strictness of cb maximality at intermediate levels

Companion to the paper draft `cb_maximality_v0_3.tex`, §6 (Observation → Theorem).

Under the hypotheses of `cb_maximality`, if the second width is smaller than `k`
(`shell w 0 < k`, which is what `K ≠ cb(k)` amounts to by the rigidity proposition), then the
cumulative inequality is **strict** at every intermediate level.  The mechanism is a strict
form of Proposition 4 / Claim K: the `s = 0` term of the summation is `E Y 0 = Y.sum`, so a strict
excess of the current shell over the shell of its own effective width propagates strictly.

* `claimK_strict`: `shellCb l κ < shell w l → shellCb (l+1) κ < shell w (l+1)`
  with `κ = kappa l (shell w l)`.
* `claimS_strict`: `shellCb i k < shell w i → shellCb (i+1) k < shell w (i+1)`.
* `cb_maximality_strict`: `cumShell w L ≤ cumShellCb k L` and `shell w 0 < k` give
  `cumShell w n < cumShellCb k n` for all `1 ≤ n < L`.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

/-- `Y.sum ≤ (Phi id Y).sum` (each `y` contributes `1 + ⋯ + y ≥ y`). -/
theorem sum_le_phi_id_sum (Y : Multiset ℕ) : Y.sum ≤ (Phi id Y).sum := by
  have := sum_E_le_phi_id_sum Y 1
  simpa using this

/-- Strict Proposition 4: if the shell strictly exceeds the shell of its effective width, so does
the uniform extension at the next level. -/
theorem shellCb_succ_kappa_lt_phi_id (l : ℕ) (Y : Multiset ℕ) (hW : Wpred l Y)
    (hs : shellCb l (kappa l Y.sum) < Y.sum) :
    shellCb (l + 1) (kappa l Y.sum) < (Phi id Y).sum := by
  set κ := kappa l Y.sum with hκ
  rcases Nat.eq_zero_or_pos κ with h0 | hpos
  · rw [h0, shellCb_zero]
    have h1 : 0 < Y.sum := by
      rw [h0, shellCb_zero] at hs
      exact hs
    exact lt_of_lt_of_le h1 (sum_le_phi_id_sum Y)
  · have h1 := shellCb_succ_sub_eq l κ κ
    rw [Nat.sub_self, shellCb_zero, zero_add] at h1
    rw [h1]
    calc ∑ s ∈ range κ, shellCb l (κ - s) < ∑ s ∈ range κ, E Y s := by
          apply Finset.sum_lt_sum
          · intro s _
            exact hW s
          · refine ⟨0, Finset.mem_range.mpr hpos, ?_⟩
            rw [Nat.sub_zero, E_zero]
            exact hs
      _ ≤ (Phi id Y).sum := sum_E_le_phi_id_sum Y κ

/-- **Strict Claim K.** -/
theorem claimK_strict (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (l : ℕ)
    (hs : shellCb l (kappa l (shell w l)) < shell w l) :
    shellCb (l + 1) (kappa l (shell w l)) < shell w (l + 1) := by
  have hW : Wpred l (rooms w l) := by
    cases l with
    | zero => exact wpred_zero_singleton (w 0)
    | succ l =>
      have := ppred_rooms w hpos hmono l 0
      rwa [shift_zero] at this
  have h1 := shellCb_succ_kappa_lt_phi_id l (rooms w l) hW hs
  have hc := chainMap_strictMono (hpos l) (hmono (Nat.le_succ l))
  have h2 : (Phi id (rooms w l)).sum ≤ (Phi (chainMap (w l) (w (l + 1))) (rooms w l)).sum :=
    phi_id_sum_le_phi_sum _ (le_c hc) _
  unfold shell
  exact lt_of_lt_of_le h1 h2

/-- `shellCb (l+1)` is strictly increasing in the width. -/
theorem shellCb_succ_strictMono (l : ℕ) : StrictMono (shellCb (l + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [shellCb_succ_succ]
  have := le_shellCb l (k + 1)
  omega

/-- **Strict Claim S.** Once a shell of `K` strictly exceeds the cb(k) shell, all later shells
do. -/
theorem claimS_strict (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k i : ℕ)
    (h : shellCb i k < shell w i) : shellCb (i + 1) k < shell w (i + 1) := by
  set κ := kappa i (shell w i) with hκ
  have hk : k ≤ κ := le_kappa_of i _ k (le_of_lt h)
  rcases Nat.lt_or_ge k κ with hlt | hge
  · exact lt_of_lt_of_le (shellCb_succ_strictMono i hlt) (claimK w hpos hmono i)
  · have hkκ : κ = k := le_antisymm hge hk
    have hs : shellCb i κ < shell w i := by rw [hkκ]; exact h
    have := claimK_strict w hpos hmono i hs
    rw [← hκ, hkκ] at this
    exact this

theorem claimS_strict_iter (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k i : ℕ)
    (h : shellCb i k < shell w i) : ∀ j, i ≤ j → shellCb j k < shell w j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j _ ih => exact claimS_strict w hpos hmono k j ih

/-- **Strictness at intermediate levels.** If the second width is smaller than `k` (which, by the
rigidity proposition of the paper, is exactly the case `K ≠ cb(k)` under the hypothesis of
`cb_maximality`), the cumulative inequality is strict at every level `1 ≤ n < L`
(paper levels `2 ≤ l ≤ L_paper - 1`). -/
theorem cb_maximality_strict (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k L : ℕ)
    (hL : cumShell w L ≤ cumShellCb k L) (hk2 : shell w 0 < k) :
    ∀ n, 1 ≤ n → n < L → cumShell w n < cumShellCb k n := by
  intro n hn1 hnL
  by_contra hcon
  push_neg at hcon
  have hle : cumShell w n ≤ cumShellCb k n := cb_maximality w hpos hmono k L hL n (le_of_lt hnL)
  have heq : cumShell w n = cumShellCb k n := le_antisymm hle hcon
  -- the first shell is strictly smaller, so some later shell below `n` is strictly larger
  have h0 : shell w 0 < shellCb 0 k := by
    rw [shellCb_zero_left]; exact hk2
  have hex : ∃ i ∈ Finset.Ico 1 n, shellCb i k < shell w i := by
    by_contra hno
    push_neg at hno
    have hsum : ∑ i ∈ Finset.Ico 1 n, shell w i ≤ ∑ i ∈ Finset.Ico 1 n, shellCb i k :=
      Finset.sum_le_sum hno
    have hsplitK : cumShell w n = shell w 0 + ∑ i ∈ Finset.Ico 1 n, shell w i := by
      unfold cumShell
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hn1]
      simp
    have hsplitC : cumShellCb k n = shellCb 0 k + ∑ i ∈ Finset.Ico 1 n, shellCb i k := by
      unfold cumShellCb
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hn1]
      simp
    omega
  obtain ⟨i, hi, hlt⟩ := hex
  have hin : shellCb n k < shell w n :=
    claimS_strict_iter w hpos hmono k i hlt n (le_of_lt (Finset.mem_Ico.mp hi).2)
  -- then the cumulative count at `n + 1 ≤ L` is strictly larger, contradicting `cb_maximality`
  have hnext : cumShellCb k (n + 1) < cumShell w (n + 1) := by
    unfold cumShell cumShellCb
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    unfold cumShell cumShellCb at heq
    omega
  have := cb_maximality w hpos hmono k L hL (n + 1) hnL
  omega

end CbMax
end CbsLean
