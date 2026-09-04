import CbsLean.CbMaximality
import CbsLean.Rigidity

/-!
# Breadth-first minimal cost and its monotonicity under cumulative dominance (W1 plan, item A2)

Companion to `W1_Proof_Note_v0_1.md` §0 (cost form of Conjecture C) and Theorem 6.

## Definitions
For a shell sequence `g : ℕ → ℕ` (`g i` = number of admissible labels of length `i + 1`) let
`cum g L = ∑_{i<L} g i` be the cumulative count `N(L)`.  The breadth-first minimal cost of `n`
labels is the sum of the lengths of the `n` shortest labels.  The `m`-th shortest label has length
`min {L : m ≤ N(L)}`, so by the layer-cake formula

  `C_min(n) = ∑_{m=1}^{n} λ_m = ∑_{L ≥ 0} (n - N(L))₊`,

and the terms vanish for `L ≥ n` as soon as every shell is nonempty.  We take
`bfCost g n = ∑_{L < n} (n - cum g L)` (truncated subtraction) as the definition.

## Results
* `bfCost_mono`: cumulative dominance `N_K(L) ≤ N_cb(L)` gives `C_min^cb(n) ≤ C_min^K(n)`
  (termwise; no other input).
* `bfCost_eq_level_formula`: for `g ≥ 1`, `bfCost g n = ∑_{i<L} (i+1) g i + (L+1) r` with the
  breadth-first level `L` and remainder `r` of [B] Theorem 2.
* `coffeeBeanMinCost_eq_bfCost`: the closed form `coffeeBeanMinCost` of `Rigidity.lean` is
  `bfCost (coffeeBeanShell k)`.
* `bfCost_eq_sum_lengths`: `bfCost g n` is the sum of the lengths of the `n` shortest labels.
* `minCost_cb_le`: **cost form of Theorem 6** — for a nondecreasing width vector with `k₁ = 1`,
  if `N_K(L) ≤ N_cb(k)(L)` then `coffeeBeanMinCost k n ≤ bfCost g_K n` for every `n ≤ N_K(L)`.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

/-- Cumulative label count `N(L) = ∑_{i<L} g i`. -/
def cum (g : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ range L, g i

/-- Layer-cake breadth-first cost `∑_{L<n} (n - N(L))₊`. -/
def bfCost (g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ L ∈ range n, (n - cum g L)

@[simp] theorem cum_zero (g : ℕ → ℕ) : cum g 0 = 0 := by simp [cum]

theorem cum_succ (g : ℕ → ℕ) (L : ℕ) : cum g (L + 1) = cum g L + g L := by
  simp [cum, Finset.sum_range_succ]

theorem cum_mono (g : ℕ → ℕ) : Monotone (cum g) := by
  apply monotone_nat_of_le_succ
  intro L
  rw [cum_succ]
  exact Nat.le_add_right _ _

theorem le_cum_of_pos (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (L : ℕ) : L ≤ cum g L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [cum_succ]
    have := hg L
    omega

/-- **Monotonicity.** If `N_K(L) ≤ N_cb(L)` for every `L < n`, or both already reach `n`, then the
breadth-first cost of `cb` is at most that of `K`. -/
theorem bfCost_mono (gK gC : ℕ → ℕ) (n : ℕ)
    (h : ∀ L, L < n → cum gK L ≤ cum gC L ∨ (n ≤ cum gK L ∧ n ≤ cum gC L)) :
    bfCost gC n ≤ bfCost gK n := by
  unfold bfCost
  apply Finset.sum_le_sum
  intro L hL
  rcases h L (Finset.mem_range.mp hL) with h1 | ⟨h2, h3⟩
  · exact Nat.sub_le_sub_left h1 n
  · omega

/-! ### The level/remainder formula of [B] Theorem 2 -/

/-- Breadth-first level `max {L ≤ n : N(L) ≤ n}` (as `coffeeBeanLevel` in `Rigidity.lean`). -/
def level (g : ℕ → ℕ) (n : ℕ) : ℕ := Nat.findGreatest (fun L => cum g L ≤ n) n

theorem cum_level_le (g : ℕ → ℕ) (n : ℕ) : cum g (level g n) ≤ n :=
  Nat.findGreatest_spec (P := fun L => cum g L ≤ n) (Nat.zero_le n) (by simp)

theorem level_le (g : ℕ → ℕ) (n : ℕ) : level g n ≤ n := Nat.findGreatest_le n

/-- Beyond the level the cumulative count exceeds `n` (for `g ≥ 1`). -/
theorem lt_cum_of_level_lt (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n L : ℕ) (hL : level g n < L) :
    n < cum g L := by
  by_contra hcon
  push_neg at hcon
  have hLn : L ≤ n := le_trans (le_cum_of_pos g hg L) hcon
  have : L ≤ level g n := Nat.le_findGreatest hLn hcon
  omega

/-- Abel summation: `∑_{L ≤ M} N(L) + ∑_{i<M} (i+1) g i = (M+1) N(M)`. -/
theorem sum_cum_add_mainCost (g : ℕ → ℕ) (M : ℕ) :
    ∑ L ∈ range (M + 1), cum g L + ∑ i ∈ range M, (i + 1) * g i = (M + 1) * cum g M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => (i + 1) * g i), cum_succ]
    have : ∑ L ∈ range (M + 1), cum g L + ∑ i ∈ range M, (i + 1) * g i = (M + 1) * cum g M := ih
    nlinarith [this]

/-- Terms of the layer-cake sum beyond the level vanish, so the sum can be cut at `level + 1`. -/
theorem bfCost_eq_sum_level (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    bfCost g n = ∑ L ∈ range (level g n + 1), (n - cum g L) := by
  unfold bfCost
  have hle : level g n + 1 ≤ n + 1 := Nat.succ_le_succ (level_le g n)
  -- extend the range to n + 1 (the extra term is 0) and then cut it back
  have h1 : ∑ L ∈ range n, (n - cum g L) = ∑ L ∈ range (n + 1), (n - cum g L) := by
    rw [Finset.sum_range_succ]
    have : n - cum g n = 0 := Nat.sub_eq_zero_of_le (le_cum_of_pos g hg n)
    rw [this, add_zero]
  rw [h1]
  obtain ⟨d, hd⟩ : ∃ d, n + 1 = (level g n + 1) + d := ⟨n + 1 - (level g n + 1), by omega⟩
  rw [hd, Finset.sum_range_add]
  have hzero : ∑ x ∈ range d, (n - cum g (level g n + 1 + x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply Nat.sub_eq_zero_of_le
    exact le_of_lt (lt_cum_of_level_lt g hg n _ (by omega))
  rw [hzero, add_zero]

/-- **[B] Theorem 2 formula.** For `g ≥ 1`,
`bfCost g n = ∑_{i<L} (i+1) g i + (L+1) (n - N(L))` with `L = level g n`. -/
theorem bfCost_eq_level_formula (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    bfCost g n = ∑ i ∈ range (level g n), (i + 1) * g i
      + (level g n + 1) * (n - cum g (level g n)) := by
  rw [bfCost_eq_sum_level g hg n]
  set M := level g n with hM
  have hcum : ∀ L ∈ range (M + 1), cum g L ≤ n := by
    intro L hL
    have hLM : L ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hL)
    exact le_trans (cum_mono g hLM) (cum_level_le g n)
  have hsplit : ∑ L ∈ range (M + 1), (n - cum g L)
      = ∑ L ∈ range (M + 1), n - ∑ L ∈ range (M + 1), cum g L :=
    Finset.sum_tsub_distrib _ hcum
  rw [hsplit, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have habel := sum_cum_add_mainCost g M
  have hcM : cum g M ≤ n := cum_level_le g n
  -- (M+1) n - Σ cum = Σ (i+1) g i + (M+1)(n - cum M)   given  Σ cum + Σ (i+1) g i = (M+1) cum M
  have h1 : (M + 1) * (n - cum g M) = (M + 1) * n - (M + 1) * cum g M := Nat.mul_sub _ _ _
  have h2 : (M + 1) * cum g M ≤ (M + 1) * n := Nat.mul_le_mul_left _ hcM
  omega

/-- The closed form of `Rigidity.lean` is the layer-cake cost of the coffee-bean shells. -/
theorem coffeeBeanMinCost_eq_bfCost (k n : ℕ) (hk : 0 < k) :
    coffeeBeanMinCost k n = bfCost (coffeeBeanShell k) n := by
  have hg : ∀ i, 1 ≤ coffeeBeanShell k i := fun i => coffeeBeanShell_pos hk
  rw [bfCost_eq_level_formula _ hg]
  rfl

/-! ### `bfCost` is the sum of the lengths of the `n` shortest labels -/

/-- Length of the `m`-th breadth-first label (`m ≥ 1`): `min {L : m ≤ N(L)}`. -/
noncomputable def bfLength (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (m : ℕ) : ℕ :=
  Nat.find (⟨m, le_cum_of_pos g hg m⟩ : ∃ L, m ≤ cum g L)

theorem bfLength_eq_card (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (m : ℕ) (hm : m ≤ n) :
    bfLength g hg m = ((range n).filter (fun L => cum g L < m)).card := by
  unfold bfLength
  set L₀ := Nat.find (⟨m, le_cum_of_pos g hg m⟩ : ∃ L, m ≤ cum g L) with hL₀
  have hspec : m ≤ cum g L₀ := Nat.find_spec (⟨m, le_cum_of_pos g hg m⟩ : ∃ L, m ≤ cum g L)
  have hmin : ∀ L, L < L₀ → cum g L < m := fun L hL =>
    not_le.mp (Nat.find_min (⟨m, le_cum_of_pos g hg m⟩ : ∃ L, m ≤ cum g L) hL)
  have hL₀m : L₀ ≤ m := Nat.find_min' _ (le_cum_of_pos g hg m)
  have hfilt : (range n).filter (fun L => cum g L < m) = range L₀ := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hlt⟩
      by_contra hcon
      push_neg at hcon
      have := cum_mono g hcon
      omega
    · intro hL
      exact ⟨by omega, hmin L hL⟩
  rw [hfilt, Finset.card_range]

/-- **Layer cake.** `bfCost g n = ∑_{m=1}^{n} (length of the m-th shortest label)`. -/
theorem bfCost_eq_sum_lengths (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    bfCost g n = ∑ m ∈ range n, bfLength g hg (m + 1) := by
  unfold bfCost
  have hcard : ∀ m ∈ range n, bfLength g hg (m + 1)
      = ((range n).filter (fun L => cum g L < m + 1)).card := by
    intro m hm
    exact bfLength_eq_card g hg (m + 1) (Finset.mem_range.mp hm)
  rw [Finset.sum_congr rfl hcard]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L hL
  -- ∑_{m<n} [cum g L < m+1] = ∑_{m<n} [cum g L ≤ m] = n - cum g L
  have : ∑ m ∈ range n, (if cum g L < m + 1 then 1 else 0)
      = ((range n).filter (fun m => cum g L ≤ m)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro m _
    simp only [Nat.lt_succ_iff]
  rw [this]
  have hIco : (range n).filter (fun m => cum g L ≤ m) = Finset.Ico (cum g L) n := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  rw [hIco, Nat.card_Ico]

/-! ### Cost form of Theorem 6 -/

/-- Shell sequence of the width vector, including the root label: `g_K 0 = 1`,
`g_K (i+1) = shell w i` (number of labels of length `i + 2`). -/
def shellK (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => shell w i

theorem cum_shellK (w : ℕ → ℕ) (L : ℕ) : cum (shellK w) (L + 1) = 1 + cumShell w L := by
  unfold cum cumShell
  rw [Finset.sum_range_succ']
  simp [shellK, add_comm]

theorem coffeeBeanShell_succ_eq (k l : ℕ) (hk : 0 < k) :
    coffeeBeanShell k (l + 1) = shellCb l k := by
  unfold coffeeBeanShell shellCb
  have h1 : k + (l + 1) - 1 = k + l := by omega
  rw [h1]
  have h2 : k + l - (k - 1) = l + 1 := by omega
  rw [← Nat.choose_symm (by omega : k - 1 ≤ k + l), h2]

theorem cum_coffeeBeanShell (k L : ℕ) (hk : 0 < k) :
    cum (coffeeBeanShell k) (L + 1) = 1 + cumShellCb k L := by
  unfold cum cumShellCb
  rw [Finset.sum_range_succ']
  have h0 : coffeeBeanShell k 0 = 1 := by
    unfold coffeeBeanShell
    have : k + 0 - 1 = k - 1 := by omega
    rw [this, Nat.choose_self]
  rw [h0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coffeeBeanShell_succ_eq k i hk

theorem shellK_pos (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (i : ℕ) :
    1 ≤ shellK w i := by
  cases i with
  | zero => simp [shellK]
  | succ i =>
    change 1 ≤ shell w i
    have h1 : shellCb 0 1 ≤ shell w 0 := by
      unfold shell rooms
      simp only [shellCb, Multiset.sum_singleton]
      have : Nat.choose (1 + 0) (0 + 1) = 1 := by decide
      rw [this]
      exact hpos 0
    have h2 := claimS_iter w hpos hmono 1 0 h1 i (Nat.zero_le i)
    have h3 : 1 ≤ shellCb i 1 := by
      unfold shellCb
      have : Nat.choose (1 + i) (i + 1) = 1 := by
        rw [add_comm]; exact Nat.choose_self _
      omega
    exact le_trans h3 h2

/-- **Cost form of Theorem 6.** For a nondecreasing width vector with `k₁ = 1` and `k ≥ 1`: if
`N_K(L+1) ≤ N_cb(k)(L+1)`, then for every `n ≤ N_K(L+1)` the coffee-bean minimal cost is at most
the breadth-first cost of `K`. -/
theorem minCost_cb_le (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k L : ℕ)
    (hk : 0 < k) (hL : cumShell w L ≤ cumShellCb k L) :
    ∀ n, n ≤ 1 + cumShell w L → coffeeBeanMinCost k n ≤ bfCost (shellK w) n := by
  intro n hn
  rw [coffeeBeanMinCost_eq_bfCost k n hk]
  apply bfCost_mono
  intro L' _
  cases L' with
  | zero => left; simp
  | succ L' =>
    rw [cum_shellK, cum_coffeeBeanShell k L' hk]
    rcases Nat.lt_or_ge L' (L + 1) with h | h
    · left
      have := cb_maximality w hpos hmono k L hL L' (Nat.lt_succ_iff.mp h)
      omega
    · right
      have hLL : L ≤ L' := by omega
      have hK : cumShell w L ≤ cumShell w L' := by
        unfold cumShell
        exact Finset.sum_le_sum_of_subset (Finset.range_mono hLL)
      have hC : cumShellCb k L ≤ cumShellCb k L' := by
        unfold cumShellCb
        exact Finset.sum_le_sum_of_subset (Finset.range_mono hLL)
      omega

end CbMax
end CbsLean
