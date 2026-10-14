import CbsLean.NestedChainsComplement

/-!
# Theorem 4.3 for every word of strict and weak relations

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), §4 (identity (2), Theorem 4.3).

## Conventions

* A word is `ε : ℕ → Bool`; `ε i = true` means `q i < q (i + 1)` and `ε i = false` means
  `q i ≤ q (i + 1)` (levels from `0`).  Chains of length `D` use the letters `ε 0, …, ε (D - 2)`
  (`hW_congr`), so the paper's words `ε≤` and `ε<` of length `D` are `ε` with `ε (D - 1)` set
  to `false` or `true`.
* `endsW A ε n v` counts the `ε`-chains `q 0, …, q n` with `q i ∈ A i` and `q n = v`, and
  `hW A ε D` the `ε`-chains of length `D` (`hW_eq_card`).

## Main results

| paper | Lean |
|---|---|
| `h^ε_A(D)` counts `ε`-chains | `hW_eq_card` |
| words `(≤, …)`, `(<, …)` | `hW_false`, `hW_true` |
| identity (2) | `hW_weak_eq` |
| Theorem 4.3 | `complement_word_le`, `complement_word_lt` |
| Theorems 3.1 and 3.4 for every word | `macaulay_word_le`, `kk_word_lt` |
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace NestedChains

open Macaulay

variable {α : Type*} [LinearOrder α]

/-- The relation of the letter `ε i`: `<` if `ε i = true` and `≤` otherwise. -/
def wordRel (ε : ℕ → Bool) (i : ℕ) (u v : α) : Prop := if ε i = true then u < v else u ≤ v

instance (ε : ℕ → Bool) (i : ℕ) : DecidableRel (wordRel (α := α) ε i) := fun u v => by
  unfold wordRel
  infer_instance

/-- `ε`-chains of length `n + 1` ending at `v`. -/
def endsW (A : ℕ → Finset α) (ε : ℕ → Bool) : ℕ → α → ℕ := PathCount.pathEnds A (wordRel ε)

/-- `h^ε_A(D)`: the number of `ε`-chains of length `D` (`hW A ε 0 = 1`). -/
def hW (A : ℕ → Finset α) (ε : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ v ∈ A n, endsW A ε n v

theorem endsW_zero (A : ℕ → Finset α) (ε : ℕ → Bool) (v : α) :
    endsW A ε 0 v = if v ∈ A 0 then 1 else 0 := by
  rfl

theorem endsW_succ (A : ℕ → Finset α) (ε : ℕ → Bool) (n : ℕ) (v : α) :
    endsW A ε (n + 1) v = if v ∈ A (n + 1) then
      ∑ u ∈ (A n).filter (fun u => wordRel ε n u v), endsW A ε n u else 0 := by
  rfl

/-- The `ε`-chains of length `n + 1` as maps `Fin (n + 1) → α`. -/
theorem hW_eq_card (A : ℕ → Finset α) (ε : ℕ → Bool) (n : ℕ) :
    hW A ε (n + 1) = ((Fintype.piFinset fun i : Fin (n + 1) => A i).filter
      (fun q => ∀ i : Fin n, wordRel ε i (q i.castSucc) (q i.succ))).card := by
  exact (PathCount.card_paths A (wordRel ε) n).symm

/-! ### Dependence on the letters -/

theorem endsW_congr (A : ℕ → Finset α) {ε ε' : ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, ε i = ε' i) (v : α) : endsW A ε n v = endsW A ε' n v := by
  induction n generalizing v with
  | zero => rw [endsW_zero, endsW_zero]
  | succ n ih =>
    rw [endsW_succ, endsW_succ]
    have hn : ε n = ε' n := h n (Nat.lt_succ_self n)
    have hf : (A n).filter (fun u => wordRel ε n u v) =
        (A n).filter (fun u => wordRel ε' n u v) := by
      refine Finset.filter_congr fun u _ => ?_
      simp only [wordRel, hn]
    rw [hf]
    exact if_congr Iff.rfl
      (Finset.sum_congr rfl fun u _ => ih (fun i hi => h i (by omega)) u) rfl

/-- Chains of length `D` only see the letters `ε 0, …, ε (D - 2)`. -/
theorem hW_congr (A : ℕ → Finset α) {ε ε' : ℕ → Bool} {D : ℕ}
    (h : ∀ i, i + 1 < D → ε i = ε' i) : hW A ε D = hW A ε' D := by
  cases D with
  | zero => rfl
  | succ n =>
    simp only [hW]
    exact Finset.sum_congr rfl fun v _ => endsW_congr A (fun i hi => h i (by omega)) v

/-- The word `(≤, …, ≤)` gives the multichain counts. -/
theorem hW_false (A : ℕ → Finset α) (D : ℕ) : hW A (fun _ => false) D = h A D := by
  cases D with
  | zero => rfl
  | succ n =>
    simp only [hW, h]
    exact Finset.sum_congr rfl fun v _ => (ends_eq_pathEnds A n v).symm

/-- The word `(<, …, <)` gives the strict chain counts. -/
theorem hW_true (A : ℕ → Finset α) (D : ℕ) : hW A (fun _ => true) D = hS A D := by
  cases D with
  | zero => rfl
  | succ n =>
    simp only [hW, hS]
    exact Finset.sum_congr rfl fun v _ => (endsS_eq_pathEnds A n v).symm

/-! ### Restriction, peeling and identity (2) -/

theorem endsW_filter (A : ℕ → Finset α) (ε : ℕ → Bool) (P : α → Prop) [DecidablePred P]
    (hP : ∀ u v, u ≤ v → P v → P u) (n : ℕ) (v : α) :
    endsW (fun i => (A i).filter P) ε n v = if P v then endsW A ε n v else 0 := by
  have hle : ∀ i (u w : α), wordRel ε i u w → u ≤ w := by
    intro i u w huw
    unfold wordRel at huw
    split_ifs at huw
    · exact huw.le
    · exact huw
  induction n generalizing v with
  | zero =>
    rw [endsW_zero, endsW_zero]
    by_cases hv : P v <;> simp [Finset.mem_filter, hv]
  | succ n ih =>
    rw [endsW_succ, endsW_succ]
    by_cases hv : P v
    · rw [if_pos hv]
      simp only [Finset.mem_filter, hv, and_true]
      split_ifs with hm
      · rw [Finset.filter_filter]
        have hfil : (A n).filter (fun u => P u ∧ wordRel ε n u v) =
            (A n).filter (fun u => wordRel ε n u v) :=
          Finset.filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨hP u v (hle n u v h) hv, h⟩⟩
        rw [hfil]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [ih u, if_pos (hP u v (hle n u v (Finset.mem_filter.mp hu).2) hv)]
      · rfl
    · rw [if_neg hv]
      simp only [Finset.mem_filter, hv, and_false, if_false]

theorem hW_trunc_succ (A : ℕ → Finset α) (ε : ℕ → Bool) (θ : α) (n : ℕ) :
    hW (trunc A θ) ε (n + 1) = ∑ v ∈ (A n).filter (· ≤ θ), endsW A ε n v := by
  unfold hW
  refine Finset.sum_congr rfl fun v hv => ?_
  exact (endsW_filter A ε (· ≤ θ) (fun _ _ huv hv => le_trans huv hv) n v).trans
    (if_pos (Finset.mem_filter.mp hv).2)

theorem hW_truncLt_succ (A : ℕ → Finset α) (ε : ℕ → Bool) (θ : α) (n : ℕ) :
    hW (truncLt A θ) ε (n + 1) = ∑ v ∈ (A n).filter (· < θ), endsW A ε n v := by
  unfold hW
  refine Finset.sum_congr rfl fun v hv => ?_
  exact (endsW_filter A ε (· < θ) (fun _ _ huv hv => lt_of_le_of_lt huv hv) n v).trans
    (if_pos (Finset.mem_filter.mp hv).2)

/-- Step 2, weak last letter. -/
theorem endsW_succ_weak {A : ℕ → Finset α} {ε : ℕ → Bool} {n : ℕ} {θ : α}
    (hθ : θ ∈ A (n + 1)) (hε : ε n = false) :
    endsW A ε (n + 1) θ = hW (trunc A θ) ε (n + 1) := by
  rw [endsW_succ, if_pos hθ, hW_trunc_succ]
  refine Finset.sum_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
  simp [wordRel, hε]

/-- Step 2, strict last letter. -/
theorem endsW_succ_strict {A : ℕ → Finset α} {ε : ℕ → Bool} {n : ℕ} {θ : α}
    (hθ : θ ∈ A (n + 1)) (hε : ε n = true) :
    endsW A ε (n + 1) θ = hW (truncLt A θ) ε (n + 1) := by
  rw [endsW_succ, if_pos hθ, hW_truncLt_succ]
  refine Finset.sum_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
  simp [wordRel, hε]

theorem hW_weak_eq_aux (s : Finset α) (v : α) (e : α → ℕ) :
    ∑ x ∈ s.filter (· ≤ v), e x = ∑ x ∈ s.filter (· < v), e x + if v ∈ s then e v else 0 := by
  by_cases hv : v ∈ s
  · rw [if_pos hv, endsS_le_low_prefix_aux hv, Nat.add_comm]
  · rw [if_neg hv, Nat.add_zero]
    refine Finset.sum_congr (Finset.filter_congr fun x hx => ?_) fun _ _ => rfl
    exact ⟨fun hle => lt_of_le_of_ne hle fun h => hv (h ▸ hx), le_of_lt⟩

/-- **Identity (2).** `h^{ε≤}(n + 2) = h^{ε<}(n + 2) + h^ε(n + 1)` for nested `A`. -/
theorem hW_weak_eq {A : ℕ → Finset α} (hA : Monotone A) (ε : ℕ → Bool) (n : ℕ)
    (hε : ε n = false) :
    hW A ε (n + 2) = hW A (Function.update ε n true) (n + 2) + hW A ε (n + 1) := by
  have h1 : ∀ v ∈ A (n + 1), endsW A ε (n + 1) v = ∑ u ∈ (A n).filter (· < v),
      endsW A ε n u + if v ∈ A n then endsW A ε n v else 0 := by
    intro v hv
    rw [endsW_succ, if_pos hv, ← hW_weak_eq_aux]
    refine Finset.sum_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
    simp only [wordRel, hε, Bool.false_eq_true, if_false]
  have h2 : ∀ v ∈ A (n + 1), endsW A (Function.update ε n true) (n + 1) v =
      ∑ u ∈ (A n).filter (· < v), endsW A ε n u := by
    intro v hv
    rw [endsW_succ, if_pos hv]
    refine Finset.sum_congr (Finset.filter_congr fun u _ => ?_) fun u _ => ?_
    · simp only [wordRel, Function.update_self, if_true]
    · exact endsW_congr A (fun i hi => Function.update_of_ne (Nat.ne_of_lt hi) _ _) u
  have h3 : ∑ v ∈ A (n + 1), (if v ∈ A n then endsW A ε n v else 0) =
      ∑ v ∈ A n, endsW A ε n v := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hA (Nat.le_succ n))]
  change ∑ v ∈ A (n + 1), endsW A ε (n + 1) v =
    ∑ v ∈ A (n + 1), endsW A (Function.update ε n true) (n + 1) v + ∑ v ∈ A n, endsW A ε n v
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, h3]

/-- Step 1 for a weak last letter. -/
theorem sum_prefix_le_hW_succ {A : ℕ → Finset α} (hA : Monotone A) (ε : ℕ → Bool) (n : ℕ)
    (hε : ε n = false) :
    ∑ w ∈ A n, ∑ θ ∈ (A n).filter (· ≤ w), endsW A ε n θ ≤ hW A ε (n + 2) := by
  have hF : ∀ w ∈ A (n + 1),
      endsW A ε (n + 1) w = ∑ θ ∈ (A n).filter (· ≤ w), endsW A ε n θ := by
    intro w hw
    rw [endsW_succ, if_pos hw]
    refine Finset.sum_congr (Finset.filter_congr fun u _ => ?_) fun _ _ => rfl
    simp only [wordRel, hε, Bool.false_eq_true, if_false]
  calc ∑ w ∈ A n, ∑ θ ∈ (A n).filter (· ≤ w), endsW A ε n θ
      ≤ ∑ w ∈ A (n + 1), ∑ θ ∈ (A n).filter (· ≤ w), endsW A ε n θ :=
        Finset.sum_le_sum_of_subset (hA (Nat.le_succ n))
    _ = ∑ w ∈ A (n + 1), endsW A ε (n + 1) w := (Finset.sum_congr rfl hF).symm
    _ = hW A ε (n + 2) := rfl

/-! ### Theorem 4.3 -/

theorem complement_word_aux_aux {A : ℕ → Finset α} (hA : Monotone A) (ε : ℕ → Bool) (n : ℕ)
    (hε : ε n = true)
    (h : Phi (n + 1) (hW A (Function.update ε n false) (n + 1)) ≤
      hW A (Function.update ε n false) (n + 2)) :
    Phi (n + 1) (hW A ε (n + 1)) - hW A ε (n + 1) ≤ hW A ε (n + 2) := by
  have h1 := hW_weak_eq hA (Function.update ε n false) n (Function.update_self n false ε)
  have h2 : Function.update (Function.update ε n false) n true = ε := by
    funext i
    by_cases hi : i = n
    · subst hi
      rw [Function.update_self, hε]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  have h3 : hW A (Function.update ε n false) (n + 1) = hW A ε (n + 1) := by
    apply hW_congr
    intro i hi
    rw [Function.update_of_ne (by omega)]
  rw [h2, h3] at h1
  rw [h3] at h
  omega

/-- Both inequalities of Theorem 4.3 at length `D = n + 1`, for every nested sequence and word. -/
theorem complement_word_aux (n : ℕ) :
    ∀ (A : ℕ → Finset α), Monotone A → ∀ ε : ℕ → Bool,
      (ε n = false → Phi (n + 1) (hW A ε (n + 1)) ≤ hW A ε (n + 2)) ∧
      (ε n = true → Phi (n + 1) (hW A ε (n + 1)) - hW A ε (n + 1) ≤ hW A ε (n + 2)) := by
  induction n with
  | zero =>
    have key : ∀ (A : ℕ → Finset α), Monotone A → ∀ ε : ℕ → Bool, ε 0 = false →
        Phi 1 (hW A ε 1) ≤ hW A ε 2 := by
      intro A hA ε hε
      have h1 : hW A ε 1 = h A 1 := by
        rw [← hW_false A 1]
        exact hW_congr A fun i hi => absurd hi (by omega)
      have h2 : hW A ε 2 = h A 2 := by
        rw [← hW_false A 2]
        refine hW_congr A fun i hi => ?_
        obtain rfl : i = 0 := by omega
        exact hε
      rw [h1, h2, Phi_one]
      exact nested_reverse_macaulay A hA 1 le_rfl
    intro A hA ε
    exact ⟨key A hA ε, fun hε => complement_word_aux_aux hA ε 0 hε
      (key A hA _ (Function.update_self 0 false ε))⟩
  | succ n ih =>
    have key : ∀ (A : ℕ → Finset α), Monotone A → ∀ ε : ℕ → Bool, ε (n + 1) = false →
        Phi (n + 1 + 1) (hW A ε (n + 1 + 1)) ≤ hW A ε (n + 1 + 2) := by
      intro A hA ε hε
      have he : ∀ θ ∈ A (n + 1), endsW A ε (n + 1) θ ≤
          Lmax (n + 1 + 1) (∑ θ' ∈ (A (n + 1)).filter (· ≤ θ), endsW A ε (n + 1) θ') := by
        intro θ hθ
        apply le_Lmax (by omega)
        rw [Nat.add_sub_cancel]
        cases hn : ε n with
        | false =>
          have hk := (ih (trunc A θ) (trunc_mono hA θ) ε).1 hn
          rw [← endsW_succ_weak hθ hn, hW_trunc_succ] at hk
          exact hk
        | true =>
          have hk := (ih (truncLt A θ) (truncLt_mono hA θ) ε).2 hn
          rw [← endsW_succ_strict hθ hn, hW_truncLt_succ] at hk
          have hle := le_Phi (D := n + 1) (by omega) (endsW A ε (n + 1) θ)
          rw [endsS_le_low_prefix_aux hθ]
          omega
      exact (Phi_le_sum_prefix (D := n + 1 + 1) (by omega) (A (n + 1)) (endsW A ε (n + 1))
        he).trans (sum_prefix_le_hW_succ hA ε (n + 1) hε)
    intro A hA ε
    exact ⟨key A hA ε, fun hε => complement_word_aux_aux hA ε (n + 1) hε
      (key A hA _ (Function.update_self (n + 1) false ε))⟩

/-- **Theorem 4.3**, first inequality: `h^{ε≤}_A(D + 1) ≥ Φ_D(h^ε_A(D))`. -/
theorem complement_word_le (A : ℕ → Finset α) (hA : Monotone A) (ε : ℕ → Bool) (D : ℕ)
    (hD : 1 ≤ D) (hε : ε (D - 1) = false) : Phi D (hW A ε D) ≤ hW A ε (D + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  exact (complement_word_aux n A hA ε).1 (by rwa [Nat.add_sub_cancel] at hε)

/-- **Theorem 4.3**, second inequality: `h^{ε<}_A(D + 1) ≥ Φ_D(x) - x` with `x = h^ε_A(D)`. -/
theorem complement_word_lt (A : ℕ → Finset α) (hA : Monotone A) (ε : ℕ → Bool) (D : ℕ)
    (hD : 1 ≤ D) (hε : ε (D - 1) = true) :
    Phi D (hW A ε D) - hW A ε D ≤ hW A ε (D + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  exact (complement_word_aux n A hA ε).2 (by rwa [Nat.add_sub_cancel] at hε)

/-- Theorem 3.1 for every word. -/
theorem macaulay_word_le (A : ℕ → Finset α) (hA : Monotone A) (ε : ℕ → Bool) (D : ℕ)
    (hD : 1 ≤ D) (hε : ε (D - 1) = false) : up D (hW A ε D) ≤ hW A ε (D + 1) := by
  exact (up_le_Phi hD _).trans (complement_word_le A hA ε D hD hε)

/-- Theorem 3.4 for every word. -/
theorem kk_word_lt (A : ℕ → Finset α) (hA : Monotone A) (ε : ℕ → Bool) (D : ℕ)
    (hD : 1 ≤ D) (hε : ε (D - 1) = true) : kk D (hW A ε D) ≤ hW A ε (D + 1) := by
  have h1 := kk_add_self hD (hW A ε D)
  have h2 := up_le_Phi hD (hW A ε D)
  have h3 := complement_word_lt A hA ε D hD hε
  omega

end NestedChains
end CbsLean
