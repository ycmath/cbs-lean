import CbsLean.NestedChains

/-!
# Strict chains: the Kruskal–Katona analogue (paper Theorem 3.4)

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), Theorem 3.4.

`endsS A n v` counts the strict chains `q 0 < ⋯ < q n` with `q i ∈ A i` and `q n = v`, and
`hS A D` the strict chains of length `D` (`hS A 0 = 1`).  `truncLt A θ = A_i ∩ {q < θ}` agrees
with the paper's `A^{(r+1)}` for `θ = t_r` on the levels the counts use; the induction hypothesis
is applied to it.  Steps 4–5 reuse
`NestedChains.up_le_sum_prefix` with the weights `e = endsS A n`, since
`x_r = x_{r+1} + y_r ≥ y_r + y_r^{(D-1)} = y_r^⟨D-1⟩` is exactly its hypothesis.

| paper | Lean |
|---|---|
| Theorem 3.4 (inequality) | `nested_reverse_kk` |
| Theorem 3.4 (equality, `h^< = C(n, D)`) | `hS_const`, `nested_reverse_kk_const` |
| `h^<_A(D)` counts strict chains | `hS_eq_card` |
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace NestedChains

open Macaulay

variable {α : Type*} [LinearOrder α]

/-- `endsS A n v`: number of strict chains `q 0 < ⋯ < q n` with `q i ∈ A i` and `q n = v`. -/
def endsS (A : ℕ → Finset α) : ℕ → α → ℕ
  | 0, v => if v ∈ A 0 then 1 else 0
  | n + 1, v => if v ∈ A (n + 1) then ∑ u ∈ (A n).filter (· < v), endsS A n u else 0

/-- `hS A D`: number of strict chains of length `D` (the paper's `h^<_A(D)`). -/
def hS (A : ℕ → Finset α) : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ v ∈ A n, endsS A n v

/-- The truncated sequence `A_i ∩ {q < θ}`. -/
def truncLt (A : ℕ → Finset α) (θ : α) : ℕ → Finset α := fun i => (A i).filter (· < θ)

theorem endsS_filter (A : ℕ → Finset α) (P : α → Prop) [DecidablePred P]
    (hP : ∀ u v, u < v → P v → P u) (n : ℕ) (v : α) :
    endsS (fun i => (A i).filter P) n v = if P v then endsS A n v else 0 := by
  induction n generalizing v with
  | zero =>
    by_cases hv : P v <;> simp [endsS, Finset.mem_filter, hv]
  | succ n ih =>
    by_cases hv : P v
    · rw [if_pos hv]
      simp only [endsS, Finset.mem_filter, hv, and_true]
      split_ifs with hm
      · rw [Finset.filter_filter]
        have hfil : (A n).filter (fun u => P u ∧ u < v) = (A n).filter (· < v) :=
          Finset.filter_congr fun u _ => ⟨fun h => h.2, fun h => ⟨hP u v h hv, h⟩⟩
        rw [hfil]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [ih u, if_pos (hP u v (Finset.mem_filter.mp hu).2 hv)]
      · rfl
    · rw [if_neg hv]
      simp only [endsS, Finset.mem_filter, hv, and_false, if_false]

theorem endsS_truncLt (A : ℕ → Finset α) (θ : α) (n : ℕ) (v : α) :
    endsS (truncLt A θ) n v = if v < θ then endsS A n v else 0 := by
  exact endsS_filter A (· < θ) (fun _ _ huv hv => lt_trans huv hv) n v

theorem truncLt_mono {A : ℕ → Finset α} (hA : Monotone A) (θ : α) :
    Monotone (truncLt A θ) := by
  intro i j hij
  exact Finset.filter_subset_filter _ (hA hij)

theorem hS_truncLt_succ (A : ℕ → Finset α) (θ : α) (n : ℕ) :
    hS (truncLt A θ) (n + 1) = ∑ v ∈ (A n).filter (· < θ), endsS A n v := by
  unfold hS
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [endsS_truncLt, if_pos (Finset.mem_filter.mp hv).2]

/-- Step 2: the strict chains ending at `θ` are the strict chains of `A^{(r+1)}`, extended. -/
theorem endsS_succ_eq_hS_truncLt {A : ℕ → Finset α} {n : ℕ} {θ : α} (hθ : θ ∈ A (n + 1)) :
    endsS A (n + 1) θ = hS (truncLt A θ) (n + 1) := by
  rw [hS_truncLt_succ, endsS, if_pos hθ]

/-- Step 1: a strict chain extends by every element of `A n` strictly above its last entry. -/
theorem sum_strict_prefix_le_hS_succ {A : ℕ → Finset α} (hA : Monotone A) (n : ℕ) :
    ∑ w ∈ A n, ∑ θ ∈ (A n).filter (· < w), endsS A n θ ≤ hS A (n + 2) := by
  have hF : ∀ w ∈ A (n + 1),
      endsS A (n + 1) w = ∑ θ ∈ (A n).filter (· < w), endsS A n θ := by
    intro w hw
    rw [endsS, if_pos hw]
  calc ∑ w ∈ A n, ∑ θ ∈ (A n).filter (· < w), endsS A n θ
      ≤ ∑ w ∈ A (n + 1), ∑ θ ∈ (A n).filter (· < w), endsS A n θ :=
        Finset.sum_le_sum_of_subset (hA (Nat.le_succ n))
    _ = ∑ w ∈ A (n + 1), endsS A (n + 1) w := (Finset.sum_congr rfl hF).symm
    _ = hS A (n + 2) := rfl

theorem endsS_le_low_prefix_aux {s : Finset α} {θ : α} (hθ : θ ∈ s) (e : α → ℕ) :
    ∑ x ∈ s.filter (· ≤ θ), e x = e θ + ∑ x ∈ s.filter (· < θ), e x := by
  have hins : s.filter (· ≤ θ) = insert θ (s.filter (· < θ)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hle⟩
      rcases hle.lt_or_eq with hlt | heq
      · exact Or.inr ⟨hx, hlt⟩
      · exact Or.inl heq
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨hθ, le_rfl⟩
      · exact ⟨hx, hlt.le⟩
  have hnot : θ ∉ s.filter (· < θ) := fun h => lt_irrefl θ (Finset.mem_filter.mp h).2
  rw [hins, Finset.sum_insert hnot]

/-- Step 3 for strict chains. -/
theorem endsS_le_low_prefix {A : ℕ → Finset α} (hA : Monotone A) (n : ℕ)
    (ih : n = 0 ∨ ∀ B : ℕ → Finset α, Monotone B → kk n (hS B n) ≤ hS B (n + 1))
    (θ : α) (hθ : θ ∈ A n) :
    endsS A n θ ≤ low (n + 1) (∑ θ' ∈ (A n).filter (· ≤ θ), endsS A n θ') := by
  rcases n with _ | m
  · have h1 : endsS A 0 θ ≤ ∑ θ' ∈ (A 0).filter (· ≤ θ), endsS A 0 θ' :=
      Finset.single_le_sum (f := endsS A 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨hθ, le_rfl⟩)
    have he : endsS A 0 θ = 1 := by simp [endsS, hθ]
    rw [he] at h1 ⊢
    rw [Nat.zero_add, low_one, if_neg (by omega)]
  · rcases ih with h0 | ih
    · omega
    · have key := ih (truncLt A θ) (truncLt_mono hA θ)
      rw [← endsS_succ_eq_hS_truncLt hθ, hS_truncLt_succ] at key
      have hup := kk_add_self (D := m + 1) (by omega) (endsS A (m + 1) θ)
      rw [endsS_le_low_prefix_aux hθ]
      calc endsS A (m + 1) θ = low (m + 1 + 1) (up (m + 1) (endsS A (m + 1) θ)) :=
            (low_up (by omega) _).symm
        _ ≤ _ := low_mono _ (by omega)

theorem nested_reverse_kk_aux {B : ℕ → Finset α} (hB : Monotone B) (n : ℕ)
    (he : ∀ θ ∈ B n, endsS B n θ ≤ low (n + 1) (∑ θ' ∈ (B n).filter (· ≤ θ), endsS B n θ')) :
    kk (n + 1) (hS B (n + 1)) ≤ hS B (n + 2) := by
  have h1 := up_le_sum_prefix (by omega : 1 ≤ n + 1) (B n) (endsS B n) he
  have h2 := sum_strict_prefix_le_hS_succ hB n
  have h3 : ∑ w ∈ B n, ∑ θ ∈ (B n).filter (· ≤ w), endsS B n θ =
      ∑ w ∈ B n, ∑ θ ∈ (B n).filter (· < w), endsS B n θ + ∑ w ∈ B n, endsS B n w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [endsS_le_low_prefix_aux hw, Nat.add_comm]
  have h4 := kk_add_self (D := n + 1) (by omega) (hS B (n + 1))
  have h5 : hS B (n + 1) = ∑ w ∈ B n, endsS B n w := rfl
  rw [h5] at h4 ⊢
  omega

/-- **Theorem 3.4.** For every nested sequence and `D ≥ 1`, `h^<(D+1) ≥ (h^<(D))^{(D)}`. -/
theorem nested_reverse_kk (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) :
    kk D (hS A D) ≤ hS A (D + 1) := by
  have key : ∀ n : ℕ, ∀ B : ℕ → Finset α, Monotone B →
      kk (n + 1) (hS B (n + 1)) ≤ hS B (n + 2) := by
    intro n
    induction n with
    | zero =>
      intro B hB
      exact nested_reverse_kk_aux hB 0 (endsS_le_low_prefix hB 0 (Or.inl rfl))
    | succ n ih =>
      intro B hB
      exact nested_reverse_kk_aux hB (n + 1) (endsS_le_low_prefix hB (n + 1) (Or.inr ih))
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  exact key n A hA

/-- Hockey stick along a chain with strict ranks:
`∑_{u ∈ t} C(#{u' ∈ t : u' < u}, n) = C(#t, n + 1)`. -/
theorem sum_choose_rank_lt (t : Finset α) (n : ℕ) :
    ∑ u ∈ t, Nat.choose ((t.filter (· < u)).card) n = Nat.choose t.card (n + 1) := by
  refine Finset.induction_on_max t ?_ ?_
  · rw [Finset.sum_empty, Finset.card_empty, Nat.choose_zero_succ]
  · intro a s ha ih
    have has : a ∉ s := fun hmem => lt_irrefl a (ha a hmem)
    have h1 : (insert a s).filter (· < a) = s := by
      rw [Finset.filter_insert, if_neg (lt_irrefl a)]
      exact Finset.filter_true_of_mem ha
    have h2 : ∑ u ∈ s, Nat.choose (((insert a s).filter (· < u)).card) n
        = ∑ u ∈ s, Nat.choose ((s.filter (· < u)).card) n := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.filter_insert, if_neg (not_lt.mpr (ha u hu).le)]
    rw [Finset.sum_insert has, h1, h2, ih, Finset.card_insert_of_notMem has,
      Nat.choose_succ_succ' s.card n]

theorem endsS_const (s : Finset α) (n : ℕ) {v : α} (hv : v ∈ s) :
    endsS (fun _ => s) n v = Nat.choose ((s.filter (· < v)).card) n := by
  induction n generalizing v with
  | zero => simp [endsS, hv]
  | succ n ih =>
    rw [endsS, if_pos hv]
    have h1 : ∑ u ∈ s.filter (· < v), endsS (fun _ => s) n u
        = ∑ u ∈ s.filter (· < v),
            Nat.choose (((s.filter (· < v)).filter (· < u)).card) n := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_filter] at hu
      have hf : s.filter (· < u) = (s.filter (· < v)).filter (· < u) := by
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro x _
        constructor
        · intro hx
          exact ⟨lt_trans hx hu.2, hx⟩
        · intro hx
          exact hx.2
      rw [ih hu.1, hf]
    rw [h1, sum_choose_rank_lt]

/-- For a constant sequence of an `N`-element set, `h^<(D) = C(N, D)`. -/
theorem hS_const (s : Finset α) (D : ℕ) : hS (fun _ => s) D = Nat.choose s.card D := by
  cases D with
  | zero => simp [hS]
  | succ n =>
    rw [hS, Finset.sum_congr rfl (fun v hv => endsS_const s n hv), sum_choose_rank_lt]

/-- **Theorem 3.4, equality case.** -/
theorem nested_reverse_kk_const (s : Finset α) (D : ℕ) (hD : 1 ≤ D) :
    kk D (hS (fun _ => s) D) = hS (fun _ => s) (D + 1) := by
  rw [hS_const, hS_const]
  have h1 := kk_add_self hD (Nat.choose s.card D)
  rw [up_choose hD, Nat.choose_succ_succ'] at h1
  omega

/-- The strict chains of length `n + 1`: strictly monotone maps with `q i ∈ A i`. -/
def strictChains (A : ℕ → Finset α) (n : ℕ) : Finset (Fin (n + 1) → α) :=
  (Fintype.piFinset fun i : Fin (n + 1) => A i).filter (fun q => StrictMono q)

theorem endsS_eq_pathEnds (A : ℕ → Finset α) (n : ℕ) (v : α) :
    endsS A n v = PathCount.pathEnds A (fun _ u w => u < w) n v := by
  induction n generalizing v with
  | zero => simp only [endsS, PathCount.pathEnds]
  | succ n ih =>
    simp only [endsS, PathCount.pathEnds]
    exact if_congr Iff.rfl (Finset.sum_congr rfl fun u _ => ih u) rfl

theorem hS_eq_card (A : ℕ → Finset α) (n : ℕ) : hS A (n + 1) = (strictChains A n).card := by
  have hR : PathCount.paths A (fun _ u w => u < w) n = strictChains A n := by
    ext q
    rw [PathCount.mem_paths]
    simp only [strictChains, Finset.mem_filter, Fintype.mem_piFinset, Fin.strictMono_iff_lt_succ]
  rw [← hR, PathCount.card_paths]
  simp only [hS]
  exact Finset.sum_congr rfl fun v _ => endsS_eq_pathEnds A n v

end NestedChains
end CbsLean
