import CbsLean.CbStrict

/-!
# Rigidity of cb maximality

Companion to the paper draft `cb_maximality_v0_3.tex`, §6 (Proposition 6.3, Corollary 6.4).

For positive nondecreasing widths `w` (with `w 0 = k₂`), if `k ≤ w 0` then every shell of `K` is
at least the corresponding cb(k) shell, so `cumShellCb k L ≤ cumShell w L` for every `L`; equality
at level `L` forces `w i = k` for all `i < L`, i.e. `K = cb(k)` up to that level
(`rigidity_eq_iff`).  Consequently, under the hypothesis of `cb_maximality`
(`cumShell w L ≤ cumShellCb k L`), `K ≠ cb(k)` below `L` is equivalent to `w 0 < k`, which is
the hypothesis of `cb_maximality_strict` (`cb_maximality_strict_of_ne`).

Mechanism: the all-zero prefix always has room `w l` (`self_mem_rooms`), and the chain map sends
`w l` to `w (l+1)`, so a strict increase of the width gives a strict increase of the branching sum
(`phi_id_sum_lt_phi_sum`).  The constant system `w = k` reproduces the cb shells
(`shell_const`), which gives the converse direction of the equality characterization.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

theorem shell_zero (w : ℕ → ℕ) : shell w 0 = w 0 := by
  simp [shell, rooms]

/-- The all-zero prefix has room `w l`: `w l ∈ rooms w l`. -/
theorem self_mem_rooms (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) : ∀ l, w l ∈ rooms w l := by
  intro l
  induction l with
  | zero => simp [rooms]
  | succ l ih =>
    simp only [rooms, Phi, Multiset.mem_bind, Multiset.mem_map, Multiset.mem_range]
    refine ⟨w l, ih, w l - 1, ?_, ?_⟩
    · have := hpos l
      omega
    · rw [Nat.sub_add_cancel (hpos l)]
      unfold chainMap
      exact Nat.mul_div_cancel_left _ (hpos l)

/-- Strict form of `phi_id_sum_le_phi_sum`: if some room `y` is moved strictly up by `c`, the
branching sum strictly increases. -/
theorem phi_id_sum_lt_phi_sum (c : ℕ → ℕ) (hc : ∀ i, i ≤ c i) (Y : Multiset ℕ) (y : ℕ)
    (hy : y ∈ Y) (hy0 : 0 < y) (hlt : y < c y) : (Phi id Y).sum < (Phi c Y).sum := by
  unfold Phi
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply Multiset.sum_lt_sum
  · intro z _
    apply Multiset.sum_map_le_sum_map
    intro i _
    exact hc (i + 1)
  · refine ⟨y, hy, ?_⟩
    apply Multiset.sum_lt_sum
    · intro i _
      exact hc (i + 1)
    · refine ⟨y - 1, Multiset.mem_range.mpr (by omega), ?_⟩
      rw [Nat.sub_add_cancel hy0]
      exact hlt

/-- A strict width increase `w l < w (l+1)` gives a strict shell increase over cb(k) at the next
level, as soon as cb(k) is dominated at level `l`. -/
theorem shellCb_succ_lt_shell_of_width_lt (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l)
    (hmono : Monotone w) (k l : ℕ) (hk : shellCb l k ≤ shell w l) (hw : w l < w (l + 1)) :
    shellCb (l + 1) k < shell w (l + 1) := by
  have hW : Wpred l (rooms w l) := by
    cases l with
    | zero => exact wpred_zero_singleton (w 0)
    | succ l =>
      have := ppred_rooms w hpos hmono l 0
      rwa [shift_zero] at this
  have hκ : k ≤ kappa l (shell w l) := le_kappa_of l _ k hk
  have h1 : shellCb (l + 1) k ≤ (Phi id (rooms w l)).sum :=
    le_trans (shellCb_mono (l + 1) hκ) (shellCb_succ_kappa_le_phi_id l (rooms w l) hW)
  have hc := chainMap_strictMono (hpos l) (hmono (Nat.le_succ l))
  have hcw : w l < chainMap (w l) (w (l + 1)) (w l) := by
    unfold chainMap
    rw [Nat.mul_div_cancel_left _ (hpos l)]
    exact hw
  have h2 := phi_id_sum_lt_phi_sum _ (le_c hc) (rooms w l) (w l) (self_mem_rooms w hpos l)
    (hpos l) hcw
  unfold shell
  exact lt_of_le_of_lt h1 h2

/-! ### Rigidity: `k ≤ k₂` gives domination of cb(k) -/

theorem shellCb_le_shell_of_le (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w)
    (k : ℕ) (hk : k ≤ w 0) (l : ℕ) : shellCb l k ≤ shell w l :=
  claimS_iter w hpos hmono k 0 (by rw [shellCb_zero_left, shell_zero]; exact hk) l
    (Nat.zero_le l)

theorem shellCb_lt_shell_of_lt (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w)
    (k : ℕ) (hk : k < w 0) (l : ℕ) : shellCb l k < shell w l :=
  claimS_strict_iter w hpos hmono k 0 (by rw [shellCb_zero_left, shell_zero]; exact hk) l
    (Nat.zero_le l)

/-- **Rigidity (Proposition 6.3, inequality).** `k ≤ k₂ → N_cb(k)(L) ≤ N_K(L)`. -/
theorem rigidity_le (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k : ℕ)
    (hk : k ≤ w 0) (L : ℕ) : cumShellCb k L ≤ cumShell w L := by
  unfold cumShell cumShellCb
  exact Finset.sum_le_sum (fun i _ => shellCb_le_shell_of_le w hpos hmono k hk i)

theorem rigidity_lt (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k : ℕ)
    (hk : k < w 0) (L : ℕ) (hL : 1 ≤ L) : cumShellCb k L < cumShell w L := by
  unfold cumShell cumShellCb
  apply Finset.sum_lt_sum
  · intro i _
    exact le_of_lt (shellCb_lt_shell_of_lt w hpos hmono k hk i)
  · exact ⟨0, Finset.mem_range.mpr hL, shellCb_lt_shell_of_lt w hpos hmono k hk 0⟩

/-- Equality of the cumulative counts (with `k ≤ k₂`) forces `w i = k` below `L`. -/
theorem eq_of_cumShell_eq (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k : ℕ)
    (hk : k ≤ w 0) (L : ℕ) (heq : cumShell w L = cumShellCb k L) :
    ∀ i, i < L → w i = k := by
  unfold cumShell cumShellCb at heq
  have hterm : ∀ i ∈ range L, shellCb i k = shell w i :=
    (Finset.sum_eq_sum_iff_of_le
      (fun i _ => shellCb_le_shell_of_le w hpos hmono k hk i)).mp heq.symm
  intro i
  induction i with
  | zero =>
    intro h0
    have := hterm 0 (Finset.mem_range.mpr h0)
    rw [shellCb_zero_left, shell_zero] at this
    exact this.symm
  | succ i ih =>
    intro hi
    have hwi : w i = k := ih (by omega)
    by_contra hne
    have hlt : w i < w (i + 1) := by
      have : w i ≤ w (i + 1) := hmono (Nat.le_succ i)
      omega
    have hstrict := shellCb_succ_lt_shell_of_width_lt w hpos hmono k i
      (shellCb_le_shell_of_le w hpos hmono k hk i) hlt
    have := hterm (i + 1) (Finset.mem_range.mpr hi)
    omega

/-! ### The constant system `w = k` has the cb(k) shells -/

theorem rooms_congr (w w' : ℕ → ℕ) :
    ∀ l, (∀ i, i ≤ l → w i = w' i) → rooms w l = rooms w' l := by
  intro l
  induction l with
  | zero =>
    intro h
    simp [rooms, h 0 le_rfl]
  | succ l ih =>
    intro h
    simp only [rooms]
    rw [h l (Nat.le_succ l), h (l + 1) le_rfl, ih (fun i hi => h i (by omega))]

theorem rooms_const_succ (k : ℕ) (hk : 0 < k) (l : ℕ) :
    rooms (fun _ => k) (l + 1) = Phi id (rooms (fun _ => k) l) := by
  simp only [rooms]
  congr 1
  funext i
  unfold chainMap
  exact Nat.mul_div_cancel i hk

theorem rooms_const_le (k : ℕ) (hk : 0 < k) : ∀ l, ∀ y ∈ rooms (fun _ => k) l, y ≤ k := by
  intro l
  induction l with
  | zero =>
    intro y hy
    simp [rooms] at hy
    omega
  | succ l ih =>
    intro y hy
    rw [rooms_const_succ k hk] at hy
    simp only [Phi, Multiset.mem_bind, Multiset.mem_map, Multiset.mem_range] at hy
    obtain ⟨z, hz, i, hi, rfl⟩ := hy
    have := ih z hz
    simp only [id]
    omega

/-- `E (rooms cb(k) l) s = g^{cb(k-s)}_{l}` (shifted cb rooms are cb rooms). -/
theorem E_rooms_const (k : ℕ) (hk : 0 < k) :
    ∀ l s, E (rooms (fun _ => k) l) s = shellCb l (k - s) := by
  intro l
  induction l with
  | zero =>
    intro s
    simp [rooms, E, shellCb_zero_left]
  | succ l ih =>
    intro s
    rw [rooms_const_succ k hk]
    have hle : ∀ y ∈ Phi id (rooms (fun _ => k) l), y ≤ k := by
      intro y hy
      rw [← rooms_const_succ k hk] at hy
      exact rooms_const_le k hk (l + 1) y hy
    have h0 : E (Phi id (rooms (fun _ => k) l)) (s + k) = 0 :=
      E_eq_zero_of_ge _ _ (fun y hy => le_trans (hle y hy) (by omega))
    have h1 := E_add_eq (Phi id (rooms (fun _ => k) l)) s k
    rw [h0, zero_add] at h1
    have hN : ∀ j, N (Phi id (rooms (fun _ => k) l)) (s + j + 1) = shellCb l (k - (s + j)) := by
      intro j
      rw [N_Phi strictMono_id rfl, J_id, ih]
    rw [h1, Finset.sum_congr rfl (fun j _ => hN j)]
    have h2 := shellCb_succ_sub_eq l (k - s) k
    have h3 : k - s - k = 0 := by omega
    rw [h3, shellCb_zero, zero_add] at h2
    rw [h2]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega

/-- The constant width vector `k` (i.e. cb(k)) has shells `shellCb l k`. -/
theorem shell_const (k : ℕ) (hk : 0 < k) (l : ℕ) : shell (fun _ => k) l = shellCb l k := by
  have := E_rooms_const k hk l 0
  rw [E_zero, Nat.sub_zero] at this
  exact this

/-- **Rigidity (Proposition 6.3, equality case).** With `k ≤ k₂`, the cumulative counts agree at
level `L` iff `K = cb(k)` below `L`. -/
theorem rigidity_eq_iff (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k L : ℕ)
    (hk : k ≤ w 0) : cumShell w L = cumShellCb k L ↔ ∀ i, i < L → w i = k := by
  constructor
  · exact eq_of_cumShell_eq w hpos hmono k hk L
  · intro h
    unfold cumShell cumShellCb
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hk0 : 0 < k := by
      rw [← h i hi']
      exact hpos i
    unfold shell
    rw [rooms_congr w (fun _ => k) i (fun j hj => h j (by omega))]
    exact shell_const k hk0 i

/-! ### Corollary 6.4: the strictness hypothesis is just `K ≠ cb(k)` -/

/-- Under the hypothesis of `cb_maximality`, `K ≠ cb(k)` below `L` forces `k₂ < k`. -/
theorem w_zero_lt_of_ne (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k L : ℕ)
    (hL : cumShell w L ≤ cumShellCb k L) (hne : ∃ i, i < L ∧ w i ≠ k) : w 0 < k := by
  by_contra hge
  push_neg at hge
  have h1 := rigidity_le w hpos hmono k hge L
  have heq : cumShell w L = cumShellCb k L := le_antisymm hL h1
  obtain ⟨i, hi, hne⟩ := hne
  exact hne (eq_of_cumShell_eq w hpos hmono k hge L heq i hi)

/-- **Strictness for `K ≠ cb(k)` (Theorem 6.6 in its final form).** -/
theorem cb_maximality_strict_of_ne (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w)
    (k L : ℕ) (hL : cumShell w L ≤ cumShellCb k L) (hne : ∃ i, i < L ∧ w i ≠ k) :
    ∀ n, 1 ≤ n → n < L → cumShell w n < cumShellCb k n :=
  cb_maximality_strict w hpos hmono k L hL
    (by rw [shell_zero]; exact w_zero_lt_of_ne w hpos hmono k L hL hne)

end CbMax
end CbsLean
