import CbsLean.MacaulayOps
import CbsLean.PathCount

/-!
# Nested multichains: the Macaulay-type lower bound (paper §3, Theorem 3.1)

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), §3.

## Conventions

* Levels are indexed from `0`: the paper's nested sequence `A_1 ⊆ A_2 ⊆ ⋯` is
  `A 0 ⊆ A 1 ⊆ ⋯`, i.e. `A : ℕ → Finset α` with `Monotone A`, over a linear order `α`.
* `ends A n v` is the number of multichains `q 0 ≤ ⋯ ≤ q n` with `q i ∈ A i` and `q n = v`;
  `h A D` is the number of multichains of length `D` (the paper's `h_A(D)`), with `h A 0 = 1`.
  `h_eq_card` identifies `h A (n + 1)` with the number of monotone maps
  `q : Fin (n + 1) → α` with `q i ∈ A i`.
* `trunc A θ` is the nested sequence `A_i ∩ {q ≤ θ}`.  For `θ = t_r` (the `(r+1)`-st largest
  element of the last level) its multichains of length `D` are those of the paper's `A^{(r)}`.

## Proof structure (paper Steps 1–5)

* Step 1 (rooms): `sum_prefix_le_h_succ`.
* Step 2 (peeling): `ends_succ_eq_h_trunc` (and `ends_zero_eq_one` for `D = 1`).
* Step 3 (induction): inside `nested_reverse_macaulay`, via `low_mono` and `low_up`.
* Steps 4–5: the arithmetic lemma `up_le_sum_prefix`, by induction on the last level using
  `S_D(x) ≤ x_{r+1}` and `x^⟨D⟩ = x + S_D(x)^⟨D⟩`.

## Main results

| paper | Lean |
|---|---|
| Theorem 3.1 (inequality) | `nested_reverse_macaulay` |
| Theorem 3.1 (equality for constant sequences) | `h_const`, `nested_reverse_macaulay_const` |
| Corollary 3.3 (room bound), `r < m` | `room_bound` |
| Corollary 3.3 (room bound), `r ≥ m` | `room_bound_tail` |
| Definition 1.1 (`h_A(D)` counts tuples) | `h_eq_card` |
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace NestedChains

open Macaulay

variable {α : Type*} [LinearOrder α]

/-- `ends A n v`: number of multichains `q 0 ≤ ⋯ ≤ q n` with `q i ∈ A i` and `q n = v`. -/
def ends (A : ℕ → Finset α) : ℕ → α → ℕ
  | 0, v => if v ∈ A 0 then 1 else 0
  | n + 1, v => if v ∈ A (n + 1) then ∑ u ∈ (A n).filter (· ≤ v), ends A n u else 0

/-- `h A D`: number of multichains of length `D` (the paper's `h_A(D)`); `h A 0 = 1`. -/
def h (A : ℕ → Finset α) : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ v ∈ A n, ends A n v

/-- The truncated sequence `A_i ∩ {q ≤ θ}`. -/
def trunc (A : ℕ → Finset α) (θ : α) : ℕ → Finset α := fun i => (A i).filter (· ≤ θ)

/-! ### Restriction to a lower set -/

/-- Restricting every level to a lower set `P` restricts the endpoint counts. -/
theorem ends_filter (A : ℕ → Finset α) (P : α → Prop) [DecidablePred P]
    (hP : ∀ u v, u ≤ v → P v → P u) (n : ℕ) (v : α) :
    ends (fun i => (A i).filter P) n v = if P v then ends A n v else 0 := by
  induction n generalizing v with
  | zero =>
    by_cases hv : P v <;> simp [ends, Finset.mem_filter, hv]
  | succ n ih =>
    by_cases hv : P v
    · rw [if_pos hv]
      simp only [ends, Finset.mem_filter, hv, and_true]
      split_ifs with hm
      · rw [Finset.filter_filter]
        have hfil : (A n).filter (fun u => P u ∧ u ≤ v) = (A n).filter (· ≤ v) :=
          Finset.filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨hP u v h hv, h⟩⟩
        rw [hfil]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [ih u, if_pos (hP u v (Finset.mem_filter.mp hu).2 hv)]
      · rfl
    · rw [if_neg hv]
      simp only [ends, Finset.mem_filter, hv, and_false, if_false]

theorem ends_trunc (A : ℕ → Finset α) (θ : α) (n : ℕ) (v : α) :
    ends (trunc A θ) n v = if v ≤ θ then ends A n v else 0 := by
  exact ends_filter A (· ≤ θ) (fun _ _ huv hv => le_trans huv hv) n v

theorem trunc_mono {A : ℕ → Finset α} (hA : Monotone A) (θ : α) : Monotone (trunc A θ) := by
  intro i j hij
  exact Finset.filter_subset_filter _ (hA hij)

theorem h_trunc_succ (A : ℕ → Finset α) (θ : α) (n : ℕ) :
    h (trunc A θ) (n + 1) = ∑ v ∈ (A n).filter (· ≤ θ), ends A n v := by
  unfold h
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [ends_trunc, if_pos (Finset.mem_filter.mp hv).2]

/-! ### Step 2: peeling the last element -/

theorem ends_zero_eq_one {A : ℕ → Finset α} {θ : α} (hθ : θ ∈ A 0) : ends A 0 θ = 1 := by
  simp [ends, hθ]

/-- The multichains ending at `θ ∈ A (n + 1)` are the multichains of length `n + 1` of the
truncation at `θ`, extended by `θ`. -/
theorem ends_succ_eq_h_trunc {A : ℕ → Finset α} {n : ℕ} {θ : α} (hθ : θ ∈ A (n + 1)) :
    ends A (n + 1) θ = h (trunc A θ) (n + 1) := by
  rw [h_trunc_succ, ends, if_pos hθ]

/-! ### Step 1: rooms -/

/-- **Step 1.** Every multichain of length `n + 1` extends by each element of `A n` above its
last entry (nestedness: `A n ⊆ A (n + 1)`). -/
theorem sum_prefix_le_h_succ {A : ℕ → Finset α} (hA : Monotone A) (n : ℕ) :
    ∑ w ∈ A n, ∑ θ ∈ (A n).filter (· ≤ w), ends A n θ ≤ h A (n + 2) := by
  have hF : ∀ w ∈ A (n + 1),
      ends A (n + 1) w = ∑ θ ∈ (A n).filter (· ≤ w), ends A n θ := by
    intro w hw
    rw [ends, if_pos hw]
  calc ∑ w ∈ A n, ∑ θ ∈ (A n).filter (· ≤ w), ends A n θ
      ≤ ∑ w ∈ A (n + 1), ∑ θ ∈ (A n).filter (· ≤ w), ends A n θ :=
        Finset.sum_le_sum_of_subset (hA (Nat.le_succ n))
    _ = ∑ w ∈ A (n + 1), ends A (n + 1) w := (Finset.sum_congr rfl hF).symm
    _ = h A (n + 2) := rfl

/-! ### Steps 3–5: the arithmetic of prefix sums -/

theorem up_le_sum_prefix_aux {s : Finset α} {a : α} (hlt : ∀ x ∈ s, x < a) {θ : α}
    (hθ : θ ∈ s) : (insert a s).filter (· ≤ θ) = s.filter (· ≤ θ) := by
  rw [Finset.filter_insert, if_neg (not_le.mpr (hlt θ hθ))]

theorem up_le_sum_prefix_aux2 {s : Finset α} {a : α} (hlt : ∀ x ∈ s, x < a) :
    (insert a s).filter (· ≤ a) = insert a s := by
  refine Finset.filter_true_of_mem fun x hx => ?_
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact le_rfl
  · exact (hlt x hx).le

theorem up_le_sum_prefix_aux3 {D : ℕ} {s : Finset α} {a : α} (hlt : ∀ x ∈ s, x < a)
    (e : α → ℕ) (he : e a ≤ low D (∑ θ' ∈ (insert a s).filter (· ≤ a), e θ')) :
    S D (∑ θ ∈ insert a s, e θ) ≤ ∑ θ ∈ s, e θ := by
  have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
  rw [up_le_sum_prefix_aux2 hlt] at he
  rw [Finset.sum_insert has] at he ⊢
  unfold S
  omega

theorem up_le_sum_prefix_aux4 {s : Finset α} {a : α} (hlt : ∀ x ∈ s, x < a) (e : α → ℕ) :
    ∑ θ ∈ insert a s, ∑ θ' ∈ (insert a s).filter (· ≤ θ), e θ' =
      ∑ θ ∈ insert a s, e θ + ∑ θ ∈ s, ∑ θ' ∈ s.filter (· ≤ θ), e θ' := by
  have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
  rw [Finset.sum_insert has, up_le_sum_prefix_aux2 hlt]
  congr 1
  exact Finset.sum_congr rfl fun θ hθ => by rw [up_le_sum_prefix_aux hlt hθ]

theorem up_le_sum_prefix_aux5 {s : Finset α} {a : α} (hlt : ∀ x ∈ s, x < a) (e : α → ℕ)
    {D : ℕ} (he : ∀ θ ∈ insert a s, e θ ≤ low D (∑ θ' ∈ (insert a s).filter (· ≤ θ), e θ')) :
    ∀ θ ∈ s, e θ ≤ low D (∑ θ' ∈ s.filter (· ≤ θ), e θ') := fun θ hθ => by
  rw [← up_le_sum_prefix_aux hlt hθ]
  exact he θ (Finset.mem_insert_of_mem hθ)

/-- **Steps 4–5.** Let `e` be a weight on a finite chain `T` and `X θ = ∑_{θ' ≤ θ} e θ'` its
prefix sums.  If `e θ ≤ (X θ)_⟨D⟩` for every `θ ∈ T` (Step 3), then
`(∑ e)^⟨D⟩ ≤ ∑_θ X θ`. -/
theorem up_le_sum_prefix {D : ℕ} (hD : 1 ≤ D) (T : Finset α) (e : α → ℕ)
    (he : ∀ θ ∈ T, e θ ≤ low D (∑ θ' ∈ T.filter (· ≤ θ), e θ')) :
    up D (∑ θ ∈ T, e θ) ≤ ∑ θ ∈ T, ∑ θ' ∈ T.filter (· ≤ θ), e θ' := by
  induction T using Finset.induction_on_max with
  | h0 => simp
  | step a s hlt ih =>
    have hS := up_le_sum_prefix_aux3 hlt e (he a (Finset.mem_insert_self a s))
    rw [up_le_sum_prefix_aux4 hlt, up_eq_add_up_S hD]
    exact Nat.add_le_add_left
      ((up_mono D hS).trans (ih (up_le_sum_prefix_aux5 hlt e he))) _

/-- Iterated form of Step 4: the prefix sum below the `(r+1)`-st largest element is at least
`S_D^r` of the total. -/
theorem iterate_S_le_prefix {D : ℕ} (T : Finset α) (e : α → ℕ)
    (he : ∀ θ ∈ T, e θ ≤ low D (∑ θ' ∈ T.filter (· ≤ θ), e θ')) (θ : α) (hθ : θ ∈ T) :
    (S D)^[(T.filter (θ < ·)).card] (∑ θ' ∈ T, e θ') ≤ ∑ θ' ∈ T.filter (· ≤ θ), e θ' := by
  induction T using Finset.induction_on_max generalizing θ with
  | h0 => exact absurd hθ (Finset.notMem_empty θ)
  | step a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rcases Finset.mem_insert.1 hθ with hθa | hθs
    · subst hθa
      have h0 : (insert θ s).filter (θ < ·) = ∅ := by
        refine Finset.filter_false_of_mem fun x hx => ?_
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact lt_irrefl x
        · exact not_lt.mpr (hlt x hx).le
      rw [h0, Finset.card_empty, Function.iterate_zero, id, up_le_sum_prefix_aux2 hlt]
    · have hc : (insert a s).filter (θ < ·) = insert a (s.filter (θ < ·)) := by
        rw [Finset.filter_insert, if_pos (hlt θ hθs)]
      rw [hc, Finset.card_insert_of_notMem fun h => has (Finset.mem_filter.1 h).1,
        Function.iterate_succ_apply, up_le_sum_prefix_aux hlt hθs]
      exact ((S_mono D).iterate _ (up_le_sum_prefix_aux3 hlt e (he a
        (Finset.mem_insert_self a s)))).trans (ih (up_le_sum_prefix_aux5 hlt e he) θ hθs)

/-! ### Theorem 3.1 -/

/-- Step 3: the hypothesis of `up_le_sum_prefix` holds on the last level, given Theorem 3.1
one degree lower for every nested sequence. -/
theorem ends_le_low_prefix {A : ℕ → Finset α} (hA : Monotone A) (n : ℕ)
    (ih : n = 0 ∨ ∀ B : ℕ → Finset α, Monotone B → up n (h B n) ≤ h B (n + 1))
    (θ : α) (hθ : θ ∈ A n) :
    ends A n θ ≤ low (n + 1) (∑ θ' ∈ (A n).filter (· ≤ θ), ends A n θ') := by
  rcases n with _ | m
  · have h1 : ends A 0 θ ≤ ∑ θ' ∈ (A 0).filter (· ≤ θ), ends A 0 θ' :=
      Finset.single_le_sum (f := ends A 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨hθ, le_rfl⟩)
    rw [ends_zero_eq_one hθ] at h1 ⊢
    rw [Nat.zero_add, low_one, if_neg (by omega)]
  · rcases ih with h0 | ih
    · omega
    · have key := ih (trunc A θ) (trunc_mono hA θ)
      rw [← ends_succ_eq_h_trunc hθ, h_trunc_succ] at key
      calc ends A (m + 1) θ = low (m + 1 + 1) (up (m + 1) (ends A (m + 1) θ)) :=
            (low_up (by omega) _).symm
        _ ≤ _ := low_mono _ key

/-- **Theorem 3.1.** For every nested sequence `A` and `D ≥ 1`, `h_A(D+1) ≥ h_A(D)^⟨D⟩`. -/
theorem nested_reverse_macaulay (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) :
    up D (h A D) ≤ h A (D + 1) := by
  have key : ∀ n : ℕ, ∀ B : ℕ → Finset α, Monotone B →
      up (n + 1) (h B (n + 1)) ≤ h B (n + 2) := by
    intro n
    induction n with
    | zero =>
      intro B hB
      exact (up_le_sum_prefix le_rfl (B 0) (ends B 0)
        (ends_le_low_prefix hB 0 (Or.inl rfl))).trans (sum_prefix_le_h_succ hB 0)
    | succ n ih =>
      intro B hB
      exact (up_le_sum_prefix (by omega) (B (n + 1)) (ends B (n + 1))
        (ends_le_low_prefix hB (n + 1) (Or.inr ih))).trans (sum_prefix_le_h_succ hB (n + 1))
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  exact key n A hA

/-- **Corollary 3.3 (room bound), `r < m`.** For `θ` in the last level `A (D - 1)` with exactly `r`
larger elements there, the multichains of length `D` whose last entry is `≤ θ` (room `≥ r`)
number at least `S_D^r(h_A(D))`. -/
theorem room_bound (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) (θ : α)
    (hθ : θ ∈ A (D - 1)) :
    (S D)^[((A (D - 1)).filter (θ < ·)).card] (h A D) ≤ h (trunc A θ) D := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hθ ⊢
  rw [h_trunc_succ]
  have ih : n = 0 ∨ ∀ B : ℕ → Finset α, Monotone B → up n (h B n) ≤ h B (n + 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr (fun B hB => nested_reverse_macaulay B hB n hn)
  exact iterate_S_le_prefix (A n) (ends A n) (ends_le_low_prefix hA n ih) θ hθ

/-- Arithmetic form of Step 4 beyond the last element: `S_D^{#T}(∑ e) = 0`. -/
theorem iterate_S_card_eq_zero {D : ℕ} (T : Finset α) (e : α → ℕ)
    (he : ∀ θ ∈ T, e θ ≤ low D (∑ θ' ∈ T.filter (· ≤ θ), e θ')) :
    (S D)^[T.card] (∑ θ ∈ T, e θ) = 0 := by
  induction T using Finset.induction_on_max with
  | h0 => simp
  | step a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hfa : (insert a s).filter (· ≤ a) = insert a s :=
      Finset.filter_true_of_mem fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact (hlt x hx).le
    have hfθ : ∀ θ ∈ s, (insert a s).filter (· ≤ θ) = s.filter (· ≤ θ) := by
      intro θ hθ
      rw [Finset.filter_insert, if_neg (not_le.mpr (hlt θ hθ))]
    have hs : ∀ θ ∈ s, e θ ≤ low D (∑ θ' ∈ s.filter (· ≤ θ), e θ') := by
      intro θ hθ
      rw [← hfθ θ hθ]
      exact he θ (Finset.mem_insert_of_mem hθ)
    have hea := he a (Finset.mem_insert_self a s)
    rw [hfa, Finset.sum_insert ha] at hea
    have hS : S D (e a + ∑ θ ∈ s, e θ) ≤ ∑ θ ∈ s, e θ := by
      unfold S
      omega
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, Function.iterate_succ_apply]
    exact Nat.le_zero.mp ((ih hs).symm ▸ ((S_mono D).iterate s.card hS))

/-- **Corollary 3.3, case `r ≥ m`.** When `r` is at least the number `m` of elements of the last
level `A (D - 1)`, no multichain has room `≥ r`, and indeed `S_D^r(h_A(D)) = 0`. -/
theorem room_bound_tail (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) (r : ℕ)
    (hr : (A (D - 1)).card ≤ r) : (S D)^[r] (h A D) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hr
  have ih : n = 0 ∨ ∀ B : ℕ → Finset α, Monotone B → up n (h B n) ≤ h B (n + 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr (fun B hB => nested_reverse_macaulay B hB n hn)
  have h0 := iterate_S_card_eq_zero (A n) (ends A n) (ends_le_low_prefix hA n ih)
  have hit : ∀ k, (S (n + 1))^[k] 0 = 0 := fun k => Function.iterate_fixed (S_zero_right _) k
  obtain ⟨k, rfl⟩ : ∃ k, r = (A n).card + k := ⟨r - (A n).card, by omega⟩
  have hh : h A (n + 1) = ∑ v ∈ A n, ends A n v := rfl
  rw [Nat.add_comm (A n).card k, Function.iterate_add_apply, hh, h0, hit]

/-! ### Equality for constant sequences -/

/-- Hockey stick along a chain: `∑_{u ∈ t} C(#{u' ∈ t : u' ≤ u} + n - 1, n) = C(#t + n, n + 1)`. -/
theorem sum_choose_rank (t : Finset α) (n : ℕ) :
    ∑ u ∈ t, Nat.choose ((t.filter (· ≤ u)).card + n - 1) n = Nat.choose (t.card + n) (n + 1) := by
  refine Finset.induction_on_max t ?_ ?_
  · rw [Finset.sum_empty, Finset.card_empty, Nat.zero_add, Nat.choose_succ_self]
  · intro a s ha ih
    have has : a ∉ s := fun hmem => lt_irrefl a (ha a hmem)
    have h1 : (insert a s).filter (· ≤ a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_refl x
      · exact (ha x hx).le
    have h2 : ∑ u ∈ s, Nat.choose (((insert a s).filter (· ≤ u)).card + n - 1) n
        = ∑ u ∈ s, Nat.choose ((s.filter (· ≤ u)).card + n - 1) n := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.filter_insert, if_neg (not_le.mpr (ha u hu))]
    have h3 : s.card + 1 + n = (s.card + n) + 1 := by omega
    have h4 : s.card + n + 1 - 1 = s.card + n := by omega
    rw [Finset.sum_insert has, h1, h2, ih, Finset.card_insert_of_notMem has, h3,
      Nat.choose_succ_succ', h4]

theorem ends_const (s : Finset α) (n : ℕ) {v : α} (hv : v ∈ s) :
    ends (fun _ => s) n v = Nat.choose ((s.filter (· ≤ v)).card + n - 1) n := by
  induction n generalizing v with
  | zero => simp [ends, hv]
  | succ n ih =>
    rw [ends, if_pos hv]
    have h1 : ∑ u ∈ s.filter (· ≤ v), ends (fun _ => s) n u
        = ∑ u ∈ s.filter (· ≤ v),
            Nat.choose (((s.filter (· ≤ v)).filter (· ≤ u)).card + n - 1) n := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_filter] at hu
      have hf : s.filter (· ≤ u) = (s.filter (· ≤ v)).filter (· ≤ u) := by
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro x _
        constructor
        · intro hx
          exact ⟨le_trans hx hu.2, hx⟩
        · intro hx
          exact hx.2
      rw [ih hu.1, hf]
    have h2 : (s.filter (· ≤ v)).card + (n + 1) - 1 = (s.filter (· ≤ v)).card + n := by
      omega
    rw [h1, sum_choose_rank, h2]

/-- For a constant sequence of an `N`-element set, `h(D) = C(N + D - 1, D)`. -/
theorem h_const (s : Finset α) (D : ℕ) :
    h (fun _ => s) D = Nat.choose (s.card + D - 1) D := by
  cases D with
  | zero => simp [h]
  | succ n =>
    have h2 : s.card + (n + 1) - 1 = s.card + n := by omega
    rw [h, Finset.sum_congr rfl (fun v hv => ends_const s n hv), sum_choose_rank, h2]

/-- **Theorem 3.1, equality case.** -/
theorem nested_reverse_macaulay_const (s : Finset α) (D : ℕ) (hD : 1 ≤ D) :
    up D (h (fun _ => s) D) = h (fun _ => s) (D + 1) := by
  have h2 : s.card + D - 1 + 1 = s.card + (D + 1) - 1 := by omega
  rw [h_const, h_const, up_choose hD, h2]

/-! ### `h` counts multichains -/

/-- The multichains of length `n + 1`: monotone maps `q : Fin (n + 1) → α` with `q i ∈ A i`. -/
def chains (A : ℕ → Finset α) (n : ℕ) : Finset (Fin (n + 1) → α) :=
  (Fintype.piFinset fun i : Fin (n + 1) => A i).filter (fun q => Monotone q)

theorem ends_eq_pathEnds (A : ℕ → Finset α) (n : ℕ) (v : α) :
    ends A n v = PathCount.pathEnds A (fun _ u w => u ≤ w) n v := by
  induction n generalizing v with
  | zero => simp only [ends, PathCount.pathEnds]
  | succ n ih =>
    simp only [ends, PathCount.pathEnds]
    exact if_congr Iff.rfl (Finset.sum_congr rfl fun u _ => ih u) rfl

/-- **Definition 1.1.** `h A (n + 1)` is the number of multichains
`q 0 ≤ q 1 ≤ ⋯ ≤ q n` with `q i ∈ A i`. -/
theorem h_eq_card (A : ℕ → Finset α) (n : ℕ) : h A (n + 1) = (chains A n).card := by
  have hR : PathCount.paths A (fun _ u w => u ≤ w) n = chains A n := by
    ext q
    rw [PathCount.mem_paths]
    simp only [chains, Finset.mem_filter, Fintype.mem_piFinset, Fin.monotone_iff_le_succ]
  rw [← hR, PathCount.card_paths]
  simp only [h]
  exact Finset.sum_congr rfl fun v _ => ends_eq_pathEnds A n v

end NestedChains
end CbsLean
