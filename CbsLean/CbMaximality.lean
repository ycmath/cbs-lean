import Mathlib

/-!
# cb maximality among single-root width-normalized label systems (W1, Theorems 5–6)

Companion to `W1_Proof_Note_v0_1.md` (v0.5, 2026-09-04), §3d.

## Conventions (all levels shifted by 2)

* `shellCb l k = Nat.choose (k + l) (l + 1)` is the coffee-bean shell count `g_{l+2}^{cb(k)}`;
  Lean level `l` is paper level `l + 2`, so `l = 1` is paper level 3 (rooms are distinct there).
  `shellCb l 0 = 0` automatically (`Nat.choose l (l+1) = 0`).
* A room multiset is a `Multiset ℕ`.  `E Y s = ∑ (y - s)` uses truncated subtraction, i.e. it is
  `∑ (y - s)₊`.  `N Y s = #{y ∈ Y : s ≤ y}`.
* `kappa l S` is the effective width `max {k : shellCb l k ≤ S}`.
* `Wpred l Y` is the shift criterion form of weak submajorization against the cb rooms
  (Lemma 6 of the note together with identity (I1)); `Lam l Y` is the 1-Lipschitz property of the
  effective width under shifts; `Ppred l Y` is `Wpred` for every shift.
* `Phi c Y` is the branching map `⊎_{y ∈ Y} {c 1, …, c y}` for a strictly increasing `c`
  with `c 0 = 0`.

## Status
All of §3d is formalized: identities, telescoping, Lemma A, Lemma B, Lemma C, Lemma D,
Theorem 5 (`ppred_rooms`), Proposition 4 in summation form, Claim K, Claim S and Theorem 6
(`cb_maximality`, cumulative dominance = Conjecture C).  Label counts are represented by room sums
(`shell w l = (rooms w l).sum`); the identification with the VW `digitBox` counts is not formalized
here.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

/-- `g_{l+2}^{cb(k)} = C(k + l, l + 1)`. -/
def shellCb (l k : ℕ) : ℕ := Nat.choose (k + l) (l + 1)

@[simp] theorem shellCb_zero (l : ℕ) : shellCb l 0 = 0 := by
  simp [shellCb]

/-- (I2) Pascal: `g_{l+3}^{cb(k+1)} = g_{l+3}^{cb(k)} + g_{l+2}^{cb(k+1)}`. -/
theorem shellCb_succ_succ (l k : ℕ) :
    shellCb (l + 1) (k + 1) = shellCb (l + 1) k + shellCb l (k + 1) := by
  unfold shellCb
  have h : k + 1 + (l + 1) = (k + l + 1) + 1 := by ring
  rw [h, Nat.choose_succ_succ]
  have h2 : k + (l + 1) = k + l + 1 := by ring
  have h3 : k + 1 + l = k + l + 1 := by ring
  rw [h2, h3]
  ring

/-- Hockey stick: `g_{l+3}^{cb(k)} = ∑_{i < k} g_{l+2}^{cb(i+1)}`. -/
theorem shellCb_succ_eq_sum (l k : ℕ) :
    shellCb (l + 1) k = ∑ i ∈ range k, shellCb l (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [shellCb_succ_succ, ih, Finset.sum_range_succ]

/-- `shellCb l` is monotone in the width. -/
theorem shellCb_mono (l : ℕ) : Monotone (shellCb l) := by
  intro a b hab
  unfold shellCb
  exact Nat.choose_le_choose (l + 1) (Nat.add_le_add_right hab l)

/-- `k ≤ shellCb l k` for every level (used to bound the effective width). -/
theorem le_shellCb (l k : ℕ) : k ≤ shellCb l k := by
  unfold shellCb
  induction l with
  | zero => simp
  | succ l ih =>
    calc k ≤ Nat.choose (k + l) (l + 1) := ih
      _ ≤ Nat.choose (k + l + 1) (l + 1 + 1) := by
          rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; simp
          · -- choose (n+1) (m+1) ≥ choose n m  when 1 ≤ ... : use Pascal
            have : Nat.choose (k + l + 1) (l + 1 + 1)
                = Nat.choose (k + l) (l + 1) + Nat.choose (k + l) (l + 1 + 1) :=
              Nat.choose_succ_succ _ _
            omega

/-- Shifted sum `E Y s = ∑_{y ∈ Y} (y - s)₊`. -/
def E (Y : Multiset ℕ) (s : ℕ) : ℕ := (Y.map (fun y => y - s)).sum

/-- Counting function `N Y s = #{y ∈ Y : s ≤ y}`. -/
def N (Y : Multiset ℕ) (s : ℕ) : ℕ := Multiset.card (Y.filter (fun y => s ≤ y))

/-- Shift `Y^{(u)} = {(y - u)₊}`. -/
def shift (Y : Multiset ℕ) (u : ℕ) : Multiset ℕ := Y.map (fun y => y - u)

@[simp] theorem E_zero (Y : Multiset ℕ) : E Y 0 = Y.sum := by
  unfold E; simp

theorem E_shift (Y : Multiset ℕ) (u s : ℕ) : E (shift Y u) s = E Y (u + s) := by
  unfold E shift
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  simp only [Function.comp]
  omega

theorem sum_shift (Y : Multiset ℕ) (u : ℕ) : (shift Y u).sum = E Y u := by
  unfold shift E; rfl

/-- Telescoping: `E Y s = E Y (s+1) + N Y (s+1)`. -/
theorem E_succ (Y : Multiset ℕ) (s : ℕ) : E Y s = E Y (s + 1) + N Y (s + 1) := by
  unfold E N
  induction Y using Multiset.induction_on with
  | empty => simp
  | cons y Y ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    by_cases h : s + 1 ≤ y
    · rw [Multiset.filter_cons_of_pos _ h, Multiset.card_cons]
      have : y - s = (y - (s + 1)) + 1 := by omega
      rw [this]; rw [ih]; ring
    · rw [Multiset.filter_cons_of_neg _ h]
      have h1 : y - s = 0 := by omega
      have h2 : y - (s + 1) = 0 := by omega
      rw [h1, h2, ih]; ring

theorem E_antitone (Y : Multiset ℕ) : Antitone (E Y) := by
  apply antitone_nat_of_succ_le
  intro s
  rw [E_succ Y s]
  exact Nat.le_add_right _ _

/-- Finite telescoping: `E Y u = E Y (u + t) + ∑_{s < t} N Y (u + s + 1)`. -/
theorem E_add_eq (Y : Multiset ℕ) (u t : ℕ) :
    E Y u = E Y (u + t) + ∑ s ∈ range t, N Y (u + s + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ih, Finset.sum_range_succ, E_succ Y (u + t)]
    have : u + (t + 1) = u + t + 1 := by ring
    rw [this]; ring

/-- `E Y s = 0` once `s` exceeds every element. -/
theorem E_eq_zero_of_ge (Y : Multiset ℕ) (s : ℕ) (h : ∀ y ∈ Y, y ≤ s) : E Y s = 0 := by
  unfold E
  apply Multiset.sum_eq_zero
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Nat.sub_eq_zero_of_le (h y hy)

/-- Effective width `kappa l S = max {k ≤ S : shellCb l k ≤ S}`. -/
def kappa (l S : ℕ) : ℕ := Nat.findGreatest (fun k => shellCb l k ≤ S) S

theorem shellCb_kappa_le (l S : ℕ) : shellCb l (kappa l S) ≤ S := by
  unfold kappa
  exact Nat.findGreatest_spec (P := fun k => shellCb l k ≤ S) (Nat.zero_le S) (by simp)

theorem le_kappa_of (l S k : ℕ) (h : shellCb l k ≤ S) : k ≤ kappa l S := by
  unfold kappa
  exact Nat.le_findGreatest (le_trans (le_shellCb l k) h) h

theorem kappa_mono (l : ℕ) : Monotone (kappa l) := by
  intro a b hab
  exact le_kappa_of l b _ (le_trans (shellCb_kappa_le l a) hab)

/-- Shift-criterion form of weak submajorization against the cb rooms at Lean level `l`
(paper level `l+2`): `E Y s ≥ g^{cb(κ - s)}` for all `s`, with `κ = kappa l (Y.sum)`. -/
def Wpred (l : ℕ) (Y : Multiset ℕ) : Prop :=
  ∀ s : ℕ, shellCb l (kappa l Y.sum - s) ≤ E Y s

/-- 1-Lipschitz effective width under shifts, in the "for all m" form. -/
def Lam (l : ℕ) (Y : Multiset ℕ) : Prop :=
  ∀ u m : ℕ, shellCb l (m + 1) ≤ E Y u → shellCb l m ≤ E Y (u + 1)

/-- `Wpred` for every shift. -/
def Ppred (l : ℕ) (Y : Multiset ℕ) : Prop :=
  ∀ u : ℕ, Wpred l (shift Y u)

/-- **Lemma A.** `Ppred l Y → Lam l Y`. -/
theorem lam_of_ppred (l : ℕ) (Y : Multiset ℕ) (hP : Ppred l Y) : Lam l Y := by
  intro u m hm
  have hW := hP u 1
  rw [E_shift, sum_shift] at hW
  -- κ := kappa l (E Y u) ≥ m + 1
  have hk : m + 1 ≤ kappa l (E Y u) := le_kappa_of l _ _ hm
  have h1 : m ≤ kappa l (E Y u) - 1 := by omega
  exact le_trans (shellCb_mono l h1) hW

/-- Branching map: `Phi c Y = ⊎_{y ∈ Y} {c 1, …, c y}`. -/
def Phi (c : ℕ → ℕ) (Y : Multiset ℕ) : Multiset ℕ :=
  Y.bind (fun y => (Multiset.range y).map (fun i => c (i + 1)))

/-- `J c s = max {i ≤ s : c i ≤ s}` = number of `i ≥ 1` with `c i ≤ s` (for strictly increasing `c`
with `c 0 = 0`). -/
def J (c : ℕ → ℕ) (s : ℕ) : ℕ := Nat.findGreatest (fun i => c i ≤ s) s

section branching
variable {c : ℕ → ℕ} (hc : StrictMono c) (hc0 : c 0 = 0)
include hc hc0

omit hc0 in
theorem le_c (i : ℕ) : i ≤ c i := by
  induction i with
  | zero => simp
  | succ i ih => exact lt_of_le_of_lt ih (hc (Nat.lt_succ_self i))

omit hc in
theorem c_J_le (s : ℕ) : c (J c s) ≤ s := by
  unfold J
  exact Nat.findGreatest_spec (P := fun i => c i ≤ s) (Nat.zero_le s) (by simp [hc0])

omit hc0 in
theorem le_J_of (s i : ℕ) (h : c i ≤ s) : i ≤ J c s := by
  unfold J
  exact Nat.le_findGreatest (le_trans (le_c hc i) h) h

/-- `c i ≤ s ↔ i ≤ J c s`. -/
theorem c_le_iff (s i : ℕ) : c i ≤ s ↔ i ≤ J c s := by
  constructor
  · exact le_J_of hc s i
  · intro h
    exact le_trans (hc.monotone h) (c_J_le hc0 s)

/-- `J c v = i ↔ c i ≤ v < c (i+1)`. -/
theorem J_eq_iff (v i : ℕ) : J c v = i ↔ (c i ≤ v ∧ v < c (i + 1)) := by
  constructor
  · intro h
    refine ⟨(c_le_iff hc hc0 v i).2 (le_of_eq h.symm), ?_⟩
    by_contra hcon
    push_neg at hcon
    have := (c_le_iff hc hc0 v (i + 1)).1 hcon
    omega
  · rintro ⟨h1, h2⟩
    have hle : i ≤ J c v := (c_le_iff hc hc0 v i).1 h1
    have hlt : ¬ (i + 1 ≤ J c v) :=
      fun h => absurd ((c_le_iff hc hc0 v (i + 1)).2 h) (not_le.mpr h2)
    omega

/-- No drop at `v + 1`: `J` is unchanged. -/
theorem J_succ_of_not_mem (v : ℕ) (h : ∀ j, c j ≠ v + 1) : J c (v + 1) = J c v := by
  rw [J_eq_iff hc hc0]
  have h1 := c_J_le hc0 v
  have h2 : v < c (J c v + 1) := by
    by_contra hcon
    push_neg at hcon
    have := (c_le_iff hc hc0 v (J c v + 1)).1 hcon
    omega
  have h3 : c (J c v + 1) ≠ v + 1 := h _
  exact ⟨by omega, by omega⟩

/-- Drop at `v + 1 = c j`: `J (v+1) = j` and `J v = j - 1`. -/
theorem J_of_eq (j v : ℕ) (h : c j = v + 1) : J c (v + 1) = j ∧ J c v = j - 1 := by
  have hj : j ≠ 0 := by
    intro h0
    rw [h0, hc0] at h
    omega
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  constructor
  · rw [J_eq_iff hc hc0]
    refine ⟨le_of_eq h, ?_⟩
    have := hc (show j' + 1 < j' + 1 + 1 by omega)
    omega
  · rw [J_eq_iff hc hc0]
    simp only [Nat.add_sub_cancel]
    have := hc (show j' < j' + 1 by omega)
    exact ⟨by omega, by omega⟩

/-- Per chain: `#{i < y : s + 1 ≤ c (i+1)} = y - J c s`. -/
theorem card_filter_chain (y s : ℕ) :
    Multiset.card (((Multiset.range y).map (fun i => c (i + 1))).filter (fun r => s + 1 ≤ r))
      = y - J c s := by
  rw [Multiset.filter_map, Multiset.card_map]
  have hpred : ∀ i ∈ Multiset.range y,
      ((fun r => s + 1 ≤ r) ∘ fun i => c (i + 1)) i ↔ J c s ≤ i := by
    intro i _
    simp only [Function.comp]
    have hiff := c_le_iff hc hc0 s (i + 1)
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      have : c (i + 1) ≤ s := hiff.2 (by omega)
      omega
    · intro h
      by_contra hcon
      push_neg at hcon
      have : i + 1 ≤ J c s := hiff.1 (by omega)
      omega
  rw [Multiset.filter_congr hpred]
  rw [← Finset.range_val, ← Finset.filter_val, Finset.card_val]
  have hIco : Finset.filter (fun i => J c s ≤ i) (Finset.range y) = Finset.Ico (J c s) y := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  rw [hIco, Nat.card_Ico]

/-- **Lemma B.** `N (Phi c Y) (s + 1) = E Y (J c s)`. -/
theorem N_Phi (Y : Multiset ℕ) (s : ℕ) : N (Phi c Y) (s + 1) = E Y (J c s) := by
  unfold N Phi E
  rw [Multiset.filter_bind, Multiset.card_bind]
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  exact card_filter_chain hc hc0 y s

end branching

/-!
### Lemma C and Lemma D (skeletons)

Lemma C: `Lam l Y → Ppred (l+1) (Phi c Y)`.  Proof sketch in the note (§3d):
with `M = Phi c Y`, `u` fixed, `κ' = kappa (l+1) (E M u)`, and
`D s = N M (u+s+1) - shellCb l (κ' - s)` (as an integer), the tail sums of `D` are the
quantities `E M (u+t) - shellCb (l+1) (κ' - t)`; `D s ≥ 0 → D (s+1) ≥ 0` between drops by Pascal and
at drops by `Lam l Y`, so the negative set of `D` is an initial segment and every tail sum is
≥ the total, which is ≥ 0 by definition of `κ'`.
-/

/-- Cumulative-vs-shell telescoping on the cb side (truncated subtraction is harmless because
`shellCb l 0 = 0`): `shellCb (l+1) κ = shellCb (l+1) (κ - t) + ∑_{s<t} shellCb l (κ - s)`. -/
theorem shellCb_succ_sub_eq (l κ t : ℕ) :
    shellCb (l + 1) κ = shellCb (l + 1) (κ - t) + ∑ s ∈ range t, shellCb l (κ - s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ih, Finset.sum_range_succ]
    rcases Nat.lt_or_ge t κ with h | h
    · have h1 : κ - t = (κ - (t + 1)) + 1 := by omega
      have h2 : shellCb (l + 1) (κ - t)
          = shellCb (l + 1) (κ - (t + 1)) + shellCb l (κ - t) := by
        rw [h1, shellCb_succ_succ]
      rw [h2]; ring
    · have h1 : κ - t = 0 := by omega
      have h2 : κ - (t + 1) = 0 := by omega
      rw [h1, h2]; simp

/-- **Lemma C.** `Lam l Y → Ppred (l+1) (Phi c Y)`. -/
theorem ppred_succ_of_lam {c : ℕ → ℕ} (hc : StrictMono c) (hc0 : c 0 = 0)
    (l : ℕ) (Y : Multiset ℕ) (hL : Lam l Y) : Ppred (l + 1) (Phi c Y) := by
  classical
  intro u t
  rw [E_shift, sum_shift]
  set M := Phi c Y with hM
  set κ := kappa (l + 1) (E M u) with hκ
  have hd : ∀ s, N M (u + s + 1) = E Y (J c (u + s)) := fun s => N_Phi hc hc0 Y (u + s)
  -- the drop lemma: nonnegativity of `D` propagates one step
  have hP : ∀ s, shellCb l (κ - s) ≤ N M (u + s + 1) →
      shellCb l (κ - (s + 1)) ≤ N M (u + (s + 1) + 1) := by
    intro s hs
    rcases Nat.eq_zero_or_pos (κ - s) with h0 | hpos
    · have : κ - (s + 1) = 0 := by omega
      rw [this]; simp
    · obtain ⟨m, hm⟩ : ∃ m, κ - s = m + 1 := ⟨κ - s - 1, by omega⟩
      have hm' : κ - (s + 1) = m := by omega
      rw [hm] at hs
      rw [hm']
      have e1 : u + (s + 1) = u + s + 1 := by ring
      by_cases hdrop : ∃ j, c j = u + s + 1
      · obtain ⟨j, hj⟩ := hdrop
        have hJ := J_of_eq hc hc0 j (u + s) hj
        rw [hd] at hs
        rw [hd, e1, hJ.1]
        rw [hJ.2] at hs
        have hj0 : j ≠ 0 := by
          intro h0
          rw [h0, hc0] at hj
          omega
        have := hL (j - 1) m hs
        have e2 : j - 1 + 1 = j := by omega
        rw [e2] at this
        exact this
      · push_neg at hdrop
        have hJ := J_succ_of_not_mem hc hc0 (u + s) hdrop
        rw [hd] at hs
        rw [hd, e1, hJ]
        exact le_trans (shellCb_mono l (Nat.le_succ m)) hs
  have hA : E M u = E M (u + t) + ∑ s ∈ range t, N M (u + s + 1) := E_add_eq M u t
  have hB : shellCb (l + 1) κ = shellCb (l + 1) (κ - t) + ∑ s ∈ range t, shellCb l (κ - s) :=
    shellCb_succ_sub_eq l κ t
  have hAB : shellCb (l + 1) κ ≤ E M u := shellCb_kappa_le _ _
  by_cases hex : ∃ s, shellCb l (κ - s) ≤ N M (u + s + 1)
  · set s₀ := Nat.find hex with hs₀
    have hs₀P : shellCb l (κ - s₀) ≤ N M (u + s₀ + 1) := Nat.find_spec hex
    have hbefore : ∀ s, s < s₀ → N M (u + s + 1) < shellCb l (κ - s) :=
      fun s hs => not_le.mp (Nat.find_min hex hs)
    have hafter : ∀ s, s₀ ≤ s → shellCb l (κ - s) ≤ N M (u + s + 1) := by
      intro s hs
      induction s with
      | zero =>
        have h0 : s₀ = 0 := by omega
        rw [h0] at hs₀P
        exact hs₀P
      | succ s ih =>
        rcases Nat.lt_or_ge s s₀ with h | h
        · have h1 : s₀ = s + 1 := by omega
          rw [h1] at hs₀P
          exact hs₀P
        · exact hP s (ih h)
    rcases Nat.lt_or_ge s₀ t with hlt | hge
    · -- tail argument beyond the first nonnegative index, with `r = κ`
      have h1 := E_add_eq M (u + t) κ
      have h2 := shellCb_succ_sub_eq l (κ - t) κ
      have h3 : κ - t - κ = 0 := by omega
      rw [h3, shellCb_zero, zero_add] at h2
      rw [h2]
      have hsum : ∑ s ∈ range κ, shellCb l (κ - t - s)
          ≤ ∑ s ∈ range κ, N M (u + t + s + 1) := by
        apply Finset.sum_le_sum
        intro s _
        have := hafter (t + s) (by omega)
        have e1 : κ - t - s = κ - (t + s) := by omega
        have e2 : u + t + s + 1 = u + (t + s) + 1 := by ring
        rw [e1, e2]
        exact this
      omega
    · -- head argument: all indices below `t` are negative
      have hsum : ∑ s ∈ range t, N M (u + s + 1) ≤ ∑ s ∈ range t, shellCb l (κ - s) := by
        apply Finset.sum_le_sum
        intro s hs
        exact le_of_lt (hbefore s (by simp only [Finset.mem_range] at hs; omega))
      omega
  · push_neg at hex
    have hsum : ∑ s ∈ range t, N M (u + s + 1) ≤ ∑ s ∈ range t, shellCb l (κ - s) := by
      apply Finset.sum_le_sum
      intro s _
      exact le_of_lt (hex s)
    omega

/-- Distinctness of a multiset (no repeated element). -/
def Distinct (Y : Multiset ℕ) : Prop := Y.Nodup

/-- Sum of a finite set of naturals with `n` elements is at least `0 + 1 + ⋯ + (n-1) = C(n,2)`. -/
theorem choose_two_le_sum (S : Finset ℕ) : Nat.choose S.card 2 ≤ ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | h0 => simp
  | step a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have hcard : s.card ≤ a := by
      have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (hlt x hx)
      simpa using Finset.card_le_card hsub
    have hch : (s.card + 1).choose 2 = s.card + s.card.choose 2 := by
      have h := Nat.choose_succ_succ s.card 1
      simpa [Nat.choose_one_right] using h
    omega

/-- Multiset version for nodup multisets. -/
theorem choose_two_le_sum_of_nodup (S : Multiset ℕ) (hS : S.Nodup) :
    Nat.choose (Multiset.card S) 2 ≤ S.sum := by
  have := choose_two_le_sum ⟨S, hS⟩
  simpa [Finset.sum_eq_multiset_sum] using this

/-- For a nodup multiset, `E Y v ≥ C(N Y v, 2)`: the excesses over `v` of the elements `≥ v`
are distinct naturals. -/
theorem choose_two_N_le_E (Y : Multiset ℕ) (hY : Y.Nodup) (v : ℕ) :
    Nat.choose (N Y v) 2 ≤ E Y v := by
  classical
  set F := Y.filter (fun y => v ≤ y) with hF
  have hEF : E Y v = (F.map (fun y => y - v)).sum := by
    unfold E
    conv_lhs => rw [← Multiset.filter_add_not (fun y => v ≤ y) Y]
    rw [Multiset.map_add, Multiset.sum_add]
    have hzero : ((Y.filter (fun y => ¬ v ≤ y)).map (fun y => y - v)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Multiset.mem_filter] at hy
      omega
    rw [hzero, add_zero]
  have hnodup : (F.map (fun y => y - v)).Nodup := by
    apply Multiset.Nodup.map_on
    · intro x hx y hy hxy
      rw [hF, Multiset.mem_filter] at hx hy
      omega
    · exact hY.filter _
  have hcard : Multiset.card (F.map (fun y => y - v)) = N Y v := by
    rw [Multiset.card_map]; rfl
  rw [hEF, ← hcard]
  exact choose_two_le_sum_of_nodup _ hnodup

/-- **Lemma D.** Distinct room sets satisfy `Ppred 1` (paper level 3). -/
theorem ppred_one_of_distinct (Y : Multiset ℕ) (hY : Distinct Y) : Ppred 1 Y := by
  intro u s
  rw [E_shift, sum_shift]
  set κ := kappa 1 (E Y u) with hκ
  induction s with
  | zero =>
    simpa using shellCb_kappa_le 1 (E Y u)
  | succ s ih =>
    rcases Nat.eq_zero_or_pos (κ - s) with h0 | hpos
    · have : κ - (s + 1) = 0 := by omega
      rw [this]; simp
    · obtain ⟨m, hm⟩ : ∃ m, κ - s = m + 1 := ⟨κ - s - 1, by omega⟩
      have hm' : κ - (s + 1) = m := by omega
      rw [hm] at ih
      rw [hm']
      have hE := E_succ Y (u + s)
      have e1 : u + (s + 1) = u + s + 1 := by ring
      rw [e1]
      have hT : shellCb 1 (m + 1) = shellCb 1 m + (m + 1) := by
        rw [shellCb_succ_succ]
        simp [shellCb]
      by_cases hN : N Y (u + s + 1) ≤ m + 1
      · omega
      · push_neg at hN
        have hdist := choose_two_N_le_E Y hY (u + s + 1)
        have h2 : Nat.choose (m + 2) 2 ≤ Nat.choose (N Y (u + s + 1)) 2 :=
          Nat.choose_le_choose 2 (by omega)
        have h3 : shellCb 1 m ≤ Nat.choose (m + 2) 2 := by
          unfold shellCb
          exact Nat.choose_le_choose 2 (by omega)
        omega

/-- Room multisets of a nondecreasing width vector with `k₁ = 1`: `rooms K 0 = {k₂}` (paper
level 2) and `rooms K (l+1) = Phi (fun i => i * k_{l+3} / k_{l+2}) (rooms K l)`.  Widths are given
as `w : ℕ → ℕ` with `w 0 = k₂`, `w 1 = k₃`, …, all positive and nondecreasing. -/
def chainMap (den num : ℕ) (i : ℕ) : ℕ := i * num / den

def rooms (w : ℕ → ℕ) : ℕ → Multiset ℕ
  | 0 => {w 0}
  | l + 1 => Phi (chainMap (w l) (w (l + 1))) (rooms w l)

theorem chainMap_strictMono {den num : ℕ} (hden : 0 < den) (h : den ≤ num) :
    StrictMono (chainMap den num) := by
  intro a b hab
  unfold chainMap
  -- (a+1) * num / den ≥ (a*num + den)/den = a*num/den + 1 > a*num/den ... via Nat.div bounds
  have h1 : a * num + den ≤ b * num := by
    have : (a + 1) * num ≤ b * num := Nat.mul_le_mul_right num hab
    nlinarith
  calc a * num / den < a * num / den + 1 := Nat.lt_succ_self _
    _ = (a * num + den) / den := by rw [Nat.add_div_right _ hden]
    _ ≤ b * num / den := Nat.div_le_div_right h1

@[simp] theorem chainMap_zero (den num : ℕ) : chainMap den num 0 = 0 := by
  simp [chainMap]

/-- **Theorem 5 (Claim W).** For positive nondecreasing widths, every room multiset satisfies
`Ppred` at its level (Lean level `l+1` ↔ paper level `l+3`; the base `l = 0` is paper level 3). -/
theorem ppred_rooms (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) :
    ∀ l, Ppred (l + 1) (rooms w (l + 1)) := by
  intro l
  induction l with
  | zero =>
    -- rooms w 1 = Phi (chainMap (w 0) (w 1)) {w 0} = {c 1, …, c (w 0)}, a distinct set
    apply ppred_one_of_distinct
    change (Phi (chainMap (w 0) (w 1)) {w 0}).Nodup
    unfold Phi
    rw [Multiset.singleton_bind]
    apply Multiset.Nodup.map _ (Multiset.nodup_range _)
    intro a b hab
    exact Nat.succ_injective ((chainMap_strictMono (hpos 0) (hmono (Nat.zero_le 1))).injective hab)
  | succ l ih =>
    have hL : Lam (l + 1) (rooms w (l + 1)) := lam_of_ppred _ _ ih
    exact ppred_succ_of_lam (chainMap_strictMono (hpos _) (hmono (Nat.le_succ _)))
      (chainMap_zero _ _) _ _ hL

/-!
### Proposition 4 (summation form), Claim K, Claim S and Theorem 6

`Wpred l Y` summed over `s < κ` gives `shellCb (l+1) κ ≤ ∑_{y ∈ Y} T(y) = (Phi id Y).sum`
(no Tomić–Weyl is needed); the actual next level `Phi c Y` has a larger sum because `i ≤ c i`.
With `shell w l = (rooms w l).sum` (the number of labels at paper level `l + 2`) this is Claim K,
Claim S follows by monotonicity of `shellCb` in the width, and Theorem 6 (cumulative dominance,
i.e. Conjecture C) follows by the induction of Proposition 3 of the note.
-/

@[simp] theorem shift_zero (Y : Multiset ℕ) : shift Y 0 = Y := by
  unfold shift
  simp

theorem J_id (s : ℕ) : J id s = s := by
  rw [J_eq_iff strictMono_id rfl]
  simp

/-- `∑_{s<t} E Y s ≤ ∑_{y ∈ Y} T(y)`. -/
theorem sum_E_le_phi_id_sum (Y : Multiset ℕ) (t : ℕ) :
    ∑ s ∈ range t, E Y s ≤ (Phi id Y).sum := by
  have h := E_add_eq (Phi id Y) 0 t
  rw [E_zero] at h
  have hN : ∀ s, N (Phi id Y) (0 + s + 1) = E Y s := by
    intro s
    rw [N_Phi strictMono_id rfl, zero_add, J_id]
  have hsum : ∑ s ∈ range t, E Y s = ∑ s ∈ range t, N (Phi id Y) (0 + s + 1) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [hN s]
  rw [hsum]
  omega

/-- **Proposition 4 (summation form).** `Wpred l Y → g^{cb(κ)}_{next} ≤ (Phi id Y).sum`. -/
theorem shellCb_succ_kappa_le_phi_id (l : ℕ) (Y : Multiset ℕ) (hW : Wpred l Y) :
    shellCb (l + 1) (kappa l Y.sum) ≤ (Phi id Y).sum := by
  set κ := kappa l Y.sum with hκ
  have h1 := shellCb_succ_sub_eq l κ κ
  rw [Nat.sub_self, shellCb_zero, zero_add] at h1
  rw [h1]
  calc ∑ s ∈ range κ, shellCb l (κ - s) ≤ ∑ s ∈ range κ, E Y s :=
        Finset.sum_le_sum (fun s _ => hW s)
    _ ≤ (Phi id Y).sum := sum_E_le_phi_id_sum Y κ

/-- Lemma 2 in room language: a larger chain map gives a larger next level. -/
theorem phi_id_sum_le_phi_sum (c : ℕ → ℕ) (hc : ∀ i, i ≤ c i) (Y : Multiset ℕ) :
    (Phi id Y).sum ≤ (Phi c Y).sum := by
  unfold Phi
  rw [Multiset.sum_bind, Multiset.sum_bind]
  apply Multiset.sum_map_le_sum_map
  intro y _
  apply Multiset.sum_map_le_sum_map
  intro i _
  exact hc (i + 1)

/-- Number of labels at paper level `l + 2`: the sum of the rooms one level below. -/
def shell (w : ℕ → ℕ) (l : ℕ) : ℕ := (rooms w l).sum

theorem shellCb_zero_left (k : ℕ) : shellCb 0 k = k := by
  simp [shellCb]

theorem kappa_zero (k : ℕ) : kappa 0 k = k := by
  apply le_antisymm
  · have := shellCb_kappa_le 0 k
    rwa [shellCb_zero_left] at this
  · exact le_kappa_of 0 k k (by rw [shellCb_zero_left])

theorem wpred_zero_singleton (k : ℕ) : Wpred 0 {k} := by
  intro s
  rw [Multiset.sum_singleton, kappa_zero, shellCb_zero_left]
  unfold E
  simp

/-- **Claim K.** `g^{cb(κ_l)}_{l+1} ≤ g_{l+1}(K)` with `κ_l` the effective width of level `l`. -/
theorem claimK (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (l : ℕ) :
    shellCb (l + 1) (kappa l (shell w l)) ≤ shell w (l + 1) := by
  have hW : Wpred l (rooms w l) := by
    cases l with
    | zero => exact wpred_zero_singleton (w 0)
    | succ l =>
      have := ppred_rooms w hpos hmono l 0
      rwa [shift_zero] at this
  have h1 := shellCb_succ_kappa_le_phi_id l (rooms w l) hW
  have hc := chainMap_strictMono (hpos l) (hmono (Nat.le_succ l))
  have h2 : (Phi id (rooms w l)).sum ≤ (Phi (chainMap (w l) (w (l + 1))) (rooms w l)).sum :=
    phi_id_sum_le_phi_sum _ (le_c hc) _
  unfold shell
  exact le_trans h1 h2

/-- **Claim S.** Once a shell of `K` reaches the cb(k) shell, the next one does too. -/
theorem claimS (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k i : ℕ)
    (h : shellCb i k ≤ shell w i) : shellCb (i + 1) k ≤ shell w (i + 1) := by
  have hk : k ≤ kappa i (shell w i) := le_kappa_of i _ k h
  exact le_trans (shellCb_mono (i + 1) hk) (claimK w hpos hmono i)

theorem claimS_iter (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k i : ℕ)
    (h : shellCb i k ≤ shell w i) : ∀ j, i ≤ j → shellCb j k ≤ shell w j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j _ ih => exact claimS w hpos hmono k j ih

/-- Cumulative label counts from paper level 2 up to paper level `n + 1`
(`N_K(n+1) = 1 + cumShell w n`, the `1` being the root label). -/
def cumShell (w : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, shell w i

def cumShellCb (k n : ℕ) : ℕ := ∑ i ∈ range n, shellCb i k

theorem cum_lt_succ (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k n : ℕ)
    (h : cumShellCb k n < cumShell w n) : cumShellCb k (n + 1) < cumShell w (n + 1) := by
  have hex : ∃ i ∈ range n, shellCb i k < shell w i := by
    by_contra hcon
    push_neg at hcon
    have : cumShell w n ≤ cumShellCb k n := Finset.sum_le_sum hcon
    omega
  obtain ⟨i, hi, hlt⟩ := hex
  have hn : shellCb n k ≤ shell w n :=
    claimS_iter w hpos hmono k i (le_of_lt hlt) n (by simp only [Finset.mem_range] at hi; omega)
  unfold cumShell cumShellCb at *
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  omega

theorem cum_lt_of_lt (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k n : ℕ)
    (h : cumShellCb k n < cumShell w n) : ∀ m, n ≤ m → cumShellCb k m < cumShell w m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact cum_lt_succ w hpos hmono k m ih

/-- **Theorem 6 (cb maximality, Conjecture C).** If the cumulative count of `K` up to some level
is at most that of `cb(k)`, the same holds at every lower level. -/
theorem cb_maximality (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) (k L : ℕ)
    (hL : cumShell w L ≤ cumShellCb k L) : ∀ n, n ≤ L → cumShell w n ≤ cumShellCb k n := by
  intro n hn
  by_contra hcon
  push_neg at hcon
  have := cum_lt_of_lt w hpos hmono k n hcon L hn
  omega

end CbMax
end CbsLean
