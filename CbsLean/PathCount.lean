import Mathlib

/-!
# Counting paths through a sequence of finite sets by their endpoint

A *path* of length `n + 1` through finite sets `G 0, G 1, …` with step relations `R 0, R 1, …`
is a map `q : Fin (n + 1) → α` with `q i ∈ G i` for every `i` and `R i (q i) (q (i + 1))` for
every `i < n`.  `pathEnds G R n v` counts the paths of length `n + 1` that end at `v`, by the
recursion on the last entry.  The main result `card_paths` identifies `∑_{v ∈ G n} pathEnds G R n v`
with the number of paths, so that counts defined by the recursion (multichains of nested sets,
lattice points of lecture hall polytopes) are the cardinalities of the corresponding tuple sets.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace PathCount

variable {α : Type*}

/-- Number of paths `q 0, …, q n` with `q i ∈ G i`, `R i (q i) (q (i + 1))` and `q n = v`. -/
def pathEnds [DecidableEq α] (G : ℕ → Finset α) (R : ℕ → α → α → Prop) [∀ n, DecidableRel (R n)] :
    ℕ → α → ℕ
  | 0, v => if v ∈ G 0 then 1 else 0
  | n + 1, v =>
      if v ∈ G (n + 1) then ∑ u ∈ (G n).filter (fun u => R n u v), pathEnds G R n u else 0

/-- The paths of length `n + 1` as a finite set of maps `Fin (n + 1) → α`. -/
def paths (G : ℕ → Finset α) (R : ℕ → α → α → Prop) [∀ n, DecidableRel (R n)] (n : ℕ) :
    Finset (Fin (n + 1) → α) :=
  (Fintype.piFinset fun i : Fin (n + 1) => G i).filter
    (fun q => ∀ i : Fin n, R i (q i.castSucc) (q i.succ))

variable (G : ℕ → Finset α) (R : ℕ → α → α → Prop) [∀ n, DecidableRel (R n)]

theorem mem_paths (n : ℕ) (q : Fin (n + 1) → α) :
    q ∈ paths G R n ↔ (∀ i : Fin (n + 1), q i ∈ G i) ∧
      ∀ i : Fin n, R i (q i.castSucc) (q i.succ) := by
  unfold paths
  simp only [Finset.mem_filter, Fintype.mem_piFinset]

/-- The paths ending at `v` are counted by `pathEnds`. -/
theorem card_paths_last [DecidableEq α] (n : ℕ) (v : α) :
    ((paths G R n).filter (fun q => q (Fin.last n) = v)).card = pathEnds G R n v := by
  induction n generalizing v with
  | zero =>
    rw [pathEnds]
    split_ifs with hv
    · rw [Finset.card_eq_one]
      refine ⟨fun _ => v, ?_⟩
      ext q
      simp only [Finset.mem_filter, mem_paths, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hq⟩
        funext i
        obtain ⟨i, hi⟩ := i
        obtain rfl : i = 0 := by omega
        exact hq
      · rintro rfl
        refine ⟨⟨fun i => ?_, fun i => i.elim0⟩, rfl⟩
        obtain ⟨i, hi⟩ := i
        obtain rfl : i = 0 := by omega
        exact hv
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq hqv
      exact hv (hqv ▸ ((mem_paths G R 0 q).1 hq).1 (Fin.last 0))
  | succ n ih =>
    rw [pathEnds]
    split_ifs with hv
    · rw [Finset.card_eq_sum_card_fiberwise (f := fun q => q (Fin.last n).castSucc)
        (t := (G n).filter (fun u => R n u v))]
      · refine Finset.sum_congr rfl fun u hu => ?_
        rw [← ih u]
        rw [Finset.mem_filter] at hu
        apply Finset.card_nbij' Fin.init (fun q' => Fin.snoc q' v)
        · intro q hq
          simp only [Finset.mem_coe, Finset.mem_filter, mem_paths] at hq ⊢
          obtain ⟨⟨⟨hG, hR⟩, -⟩, hu'⟩ := hq
          refine ⟨⟨fun i => hG i.castSucc, fun i => ?_⟩, hu'⟩
          have h := hR i.castSucc
          rw [Fin.succ_castSucc] at h
          exact h
        · intro q' hq'
          simp only [Finset.mem_coe, Finset.mem_filter, mem_paths] at hq' ⊢
          obtain ⟨⟨hG, hR⟩, hu'⟩ := hq'
          refine ⟨⟨⟨fun i => ?_, fun i => ?_⟩, Fin.snoc_last _ _⟩, ?_⟩
          · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
            · rw [Fin.snoc_castSucc]
              exact hG j
            · rw [Fin.snoc_last]
              exact hv
          · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
            · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
              exact hR j
            · rw [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last, hu']
              exact hu.2
          · rw [Fin.snoc_castSucc, hu']
        · intro q hq
          simp only [Finset.mem_coe, Finset.mem_filter] at hq
          rw [← hq.1.2]
          exact Fin.snoc_init_self q
        · intro q' _
          exact Fin.init_snoc _ _
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, mem_paths] at hq ⊢
        obtain ⟨⟨hG, hR⟩, hqv⟩ := hq
        refine ⟨hG (Fin.last n).castSucc, ?_⟩
        have h := hR (Fin.last n)
        rw [Fin.succ_last, hqv] at h
        exact h
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq hqv
      exact hv (hqv ▸ ((mem_paths G R (n + 1) q).1 hq).1 (Fin.last (n + 1)))

/-- The number of paths is the sum of `pathEnds` over the last set. -/
theorem card_paths [DecidableEq α] (n : ℕ) : (paths G R n).card = ∑ v ∈ G n, pathEnds G R n v := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => q (Fin.last n)) (t := G n)]
  · exact Finset.sum_congr rfl fun v _ => card_paths_last G R n v
  · intro q hq
    exact ((mem_paths G R n q).1 hq).1 (Fin.last n)

end PathCount
end CbsLean
