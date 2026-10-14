import CbsLean.NestedChainsStrict

/-!
# The complement form (paper §4, Theorem 4.3 for multichains and strict chains)

Companion to *A Macaulay-type lower bound for nested multichains and lecture hall polytopes*
(Yang, 2026), §2 (Lemma 2.2) and §4 (Definition 4.1, Lemma 4.2, Theorem 4.3).

## Conventions

* `ctop D x` is the least `b` with `x ≤ C(b, D)` (for `D ≥ 1`, `x ≥ 1`), i.e. the paper's
  `n + D - 1` for the band `n` of `x`; the complement is `c = C(b, D) - x`.
* `Phi D x = Φ_D(x)`: `Phi 1 x = C(x + 1, 2)`, and for `D ≥ 2`,
  `Phi D x = C(b + 1, D + 1) - (C(b, D) - x)^⟨D-1⟩` with `b = ctop D x` (`Phi D 0 = 0`).
  `Phi_band` states it without truncated subtraction.
* `Lmax D x = max {y ≤ x : Φ_{D-1}(y) ≤ x}` is the paper's `L(x)`.

## Main results

| paper | Lean |
|---|---|
| Lemma 2.2 (Galois correspondence) | `galois`, `le_up_low` |
| Lemma 2.3 (band lemma) | `Macaulay.S_lt_band` (in `MacaulayOps.lean`) |
| Definition 4.1 | `ctop`, `Phi`, `Phi_band`, `Phi_choose` |
| Lemma 4.2 (a) | `Phi_strictMono` |
| Lemma 4.2 (b) | `Lmax_eq`, `Phi_fixed` |
| Lemma 4.2 (c), inequality | `up_le_Phi` |
| Theorem 4.3, word `(≤, …, ≤)` | `nested_complement` |
| Theorem 4.3, word `(<, …, <)` (Corollary 4.4, inequality) | `nested_complement_strict` |
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace Macaulay

/-! ### Lemma 2.2 -/

/-- `c ≤ (c_⟨D+1⟩)^⟨D⟩` for `D ≥ 1`. -/
theorem le_up_low {D : ℕ} (hD : 1 ≤ D) (c : ℕ) : c ≤ up D (low (D + 1) c) := by
  induction D, hD using Nat.le_induction generalizing c with
  | base =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · obtain ⟨a, r, rfl, hr, ha⟩ := exists_split 1 hc
      rw [low_split hr ha, low_one, up_one]
      rw [Nat.choose_one_right] at hr
      rw [Nat.choose_one_right]
      by_cases hr0 : r = 0
      · subst hr0
        have h2 : a - 1 + 0 + 1 = a := by omega
        rw [if_pos rfl, h2]
        simp
      · rw [if_neg hr0, Nat.sub_add_cancel (by omega), Nat.choose_succ_succ',
          Nat.choose_one_right]
        omega
  | succ D hD ih =>
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · obtain ⟨a, r, rfl, hr, ha⟩ := exists_split (D + 1) hc
      rw [low_split hr ha]
      have e2 : Nat.choose a (D + 1 + 1) = Nat.choose a (D + 2) := rfl
      have hpas : Nat.choose a (D + 1) = Nat.choose (a - 1) D + Nat.choose (a - 1) (D + 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ a)]
        exact Nat.choose_succ_succ' (a - 1) D
      rcases Nat.lt_or_ge (low (D + 1) r) (Nat.choose (a - 1) D) with hl | hl
      · rw [up_split hl, Nat.sub_add_cancel (by omega : 1 ≤ a)]
        have := ih r
        omega
      · have h1 : up (D + 1) (Nat.choose a (D + 1)) ≤
            up (D + 1) (Nat.choose (a - 1) (D + 1) + low (D + 1) r) :=
          up_mono (D + 1) (by omega)
        rw [up_choose (by omega), Nat.choose_succ_succ'] at h1
        omega

/-- **Lemma 2.2 (Galois correspondence)**, with `d = D + 1`: `y^⟨D⟩ ≥ c ↔ y ≥ c_⟨D+1⟩`. -/
theorem galois {D : ℕ} (hD : 1 ≤ D) (c y : ℕ) : c ≤ up D y ↔ low (D + 1) c ≤ y := by
  constructor
  · intro h
    calc low (D + 1) c ≤ low (D + 1) (up D y) := low_mono (D + 1) h
      _ = y := low_up hD y
  · intro h
    exact (le_up_low hD c).trans (up_mono D h)

/-! ### Definition 4.1 -/

/-- Least `b` with `x ≤ C(b, D)` (for `D ≥ 1`, `x ≥ 1`): the paper's `n + D - 1`. -/
def ctop (D x : ℕ) : ℕ := if Nat.choose (top D x) D = x then top D x else top D x + 1

theorem ctop_spec_aux {D b : ℕ} (hD : 1 ≤ D) (hb : 1 ≤ b) :
    Nat.choose b D = Nat.choose (b - 1) (D - 1) + Nat.choose (b - 1) D := by
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.choose_succ_succ' c E

theorem ctop_spec {D x : ℕ} (hD : 1 ≤ D) (hx : 0 < x) :
    Nat.choose (ctop D x - 1) D < x ∧ x ≤ Nat.choose (ctop D x) D := by
  obtain ⟨h1, h2⟩ := top_spec hD hx
  have h3 := le_top hD hx
  unfold ctop
  split_ifs with h
  · refine ⟨?_, h.ge⟩
    have hP := ctop_spec_aux hD (by omega : 1 ≤ top D x)
    have hpos : 0 < Nat.choose (top D x - 1) (D - 1) := Nat.choose_pos (by omega)
    omega
  · refine ⟨?_, h2.le⟩
    rw [Nat.add_sub_cancel]
    omega

theorem ctop_eq_of {D x b : ℕ} (hD : 1 ≤ D) (h1 : Nat.choose (b - 1) D < x)
    (h2 : x ≤ Nat.choose b D) : ctop D x = b := by
  have hb : D ≤ b := by
    by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h2
    omega
  have hP := ctop_spec_aux hD (by omega : 1 ≤ b)
  have hpos : 0 < Nat.choose (b - 1) (D - 1) := Nat.choose_pos (by omega)
  unfold ctop
  rcases Nat.lt_or_ge x (Nat.choose b D) with hlt | hge
  · have ht : top D x = b - 1 := by
      refine top_eq_of hD (by omega) ?_
      rw [Nat.sub_add_cancel (by omega)]
      exact hlt
    rw [ht, if_neg (by omega)]
    omega
  · have ht : top D x = b := by
      refine top_eq_of hD (by omega) ?_
      have hP2 := ctop_spec_aux hD (by omega : 1 ≤ b + 1)
      simp only [Nat.add_sub_cancel] at hP2
      have hpos2 : 0 < Nat.choose b (D - 1) := Nat.choose_pos (by omega)
      omega
    rw [ht, if_pos (by omega)]

theorem le_ctop {D x : ℕ} (hD : 1 ≤ D) (hx : 0 < x) : D ≤ ctop D x := by
  have h := (ctop_spec hD hx).2
  by_contra hlt
  rw [Nat.choose_eq_zero_of_lt (by omega)] at h
  omega

/-- The complement bound `Φ_D` of Definition 4.1. -/
def Phi : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, x => Nat.choose (x + 1) 2
  | D + 2, x =>
      if x = 0 then 0
      else Nat.choose (ctop (D + 2) x + 1) (D + 3) -
        up (D + 1) (Nat.choose (ctop (D + 2) x) (D + 2) - x)

@[simp] theorem Phi_zero_right (D : ℕ) : Phi D 0 = 0 := by
  rcases D with _ | _ | D <;> simp [Phi]

theorem Phi_one (x : ℕ) : Phi 1 x = up 1 x := by
  rw [up_one]
  rfl

/-- Definition 4.1 without truncated subtraction: for `x` in the band below `C(b, D)`,
`Φ_D(x) + (C(b, D) - x)^⟨D-1⟩ = C(b + 1, D + 1)`. -/
theorem Phi_band {D x b : ℕ} (hD : 2 ≤ D) (h1 : Nat.choose (b - 1) D < x)
    (h2 : x ≤ Nat.choose b D) :
    Phi D x + up (D - 1) (Nat.choose b D - x) = Nat.choose (b + 1) (D + 1) := by
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 2 := ⟨D - 2, by omega⟩
  have hc := ctop_eq_of (by omega) h1 h2
  have hb : E + 2 ≤ b := by
    by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h2
    omega
  have hP := ctop_spec_aux (D := E + 2) (b := b) (by omega) (by omega)
  have he : E + 2 - 1 = E + 1 := by omega
  rw [he] at hP
  have hc' : Nat.choose b (E + 2) - x < Nat.choose (b - 1) (E + 1) := by omega
  have hu : up (E + 1) (Nat.choose b (E + 2) - x) ≤ Nat.choose b (E + 2) := by
    calc up (E + 1) (Nat.choose b (E + 2) - x)
        ≤ up (E + 1) (Nat.choose (b - 1) (E + 1)) := up_mono _ hc'.le
      _ = Nat.choose (b - 1 + 1) (E + 1 + 1) := up_choose (by omega) _
      _ = Nat.choose b (E + 2) := by rw [Nat.sub_add_cancel (by omega)]
  have hP2 : Nat.choose (b + 1) (E + 2 + 1) =
      Nat.choose b (E + 2) + Nat.choose b (E + 2 + 1) := Nat.choose_succ_succ' b (E + 2)
  have hdef : Phi (E + 2) x = Nat.choose (ctop (E + 2) x + 1) (E + 2 + 1) -
      up (E + 1) (Nat.choose (ctop (E + 2) x) (E + 2) - x) := by
    rw [Phi, if_neg (by omega)]
  rw [hdef, hc, he]
  omega

/-- At binomial values `Φ_D` agrees with Macaulay's operator. -/
theorem Phi_choose {D : ℕ} (hD : 1 ≤ D) (b : ℕ) :
    Phi D (Nat.choose b D) = Nat.choose (b + 1) (D + 1) := by
  rcases Nat.lt_or_ge D 2 with hD1 | hD2
  · obtain rfl : D = 1 := by omega
    rw [Phi_one, up_one, Nat.choose_one_right]
  · rcases Nat.lt_or_ge b D with hb | hb
    · rw [Nat.choose_eq_zero_of_lt hb, Nat.choose_eq_zero_of_lt (by omega : b + 1 < D + 1),
        Phi_zero_right]
    · have hP := ctop_spec_aux (by omega : 1 ≤ D) (by omega : 1 ≤ b)
      have hpos : 0 < Nat.choose (b - 1) (D - 1) := Nat.choose_pos (by omega)
      have h := Phi_band hD2 (b := b) (x := Nat.choose b D) (by omega) le_rfl
      rw [Nat.sub_self, up_zero_right, Nat.add_zero] at h
      exact h

/-! ### Lemma 4.2 -/

/-- **Lemma 4.2 (a).** `Φ_D` is strictly increasing. -/
theorem Phi_strictMono {D : ℕ} (hD : 1 ≤ D) : StrictMono (Phi D) := by
  rcases Nat.lt_or_ge D 2 with hD1 | hD2
  · obtain rfl : D = 1 := by omega
    intro u v huv
    rw [Phi_one, Phi_one]
    exact up_strictMono le_rfl huv
  · refine strictMono_nat_of_lt_succ fun x => ?_
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · have h1 : Phi D 1 = 1 := by
        have h := Phi_choose hD D
        rw [Nat.choose_self, Nat.choose_self] at h
        exact h
      rw [Phi_zero_right, h1]
      exact Nat.one_pos
    · obtain ⟨hb1, hb2⟩ := ctop_spec hD hx
      have hbD := le_ctop hD hx
      generalize ctop D x = b at hb1 hb2 hbD
      have hD1 : 1 ≤ D - 1 := by omega
      rcases Nat.lt_or_ge x (Nat.choose b D) with hlt | hge
      · have e1 := Phi_band hD2 hb1 hb2
        have e2 := Phi_band hD2 (x := x + 1) (b := b) (by omega) (by omega)
        have hc : Nat.choose b D - (x + 1) < Nat.choose b D - x := by omega
        have h3 := up_strictMono hD1 hc
        omega
      · have hxe : x = Nat.choose b D := le_antisymm hb2 hge
        have e1 : Phi D x = Nat.choose (b + 1) (D + 1) := by
          rw [hxe]
          exact Phi_choose hD b
        have hpas : Nat.choose (b + 1) D = Nat.choose b (D - 1) + Nat.choose b D := by
          obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact Nat.choose_succ_succ' b E
        have hpos : 0 < Nat.choose b (D - 1) := Nat.choose_pos (by omega)
        have e2 := Phi_band hD2 (x := x + 1) (b := b + 1)
          (by rw [Nat.add_sub_cancel]; omega) (by omega)
        have hpas2 : Nat.choose (b + 1 + 1) (D + 1) =
            Nat.choose (b + 1) D + Nat.choose (b + 1) (D + 1) :=
          Nat.choose_succ_succ' (b + 1) D
        have hc : Nat.choose (b + 1) D - (x + 1) < Nat.choose b (D - 1) := by omega
        have h3 := up_strictMono hD1 hc
        have h4 := up_choose hD1 b
        rw [Nat.sub_add_cancel (by omega : 1 ≤ D)] at h4
        omega

theorem le_Phi {D : ℕ} (hD : 1 ≤ D) (x : ℕ) : x ≤ Phi D x := by
  exact (Phi_strictMono hD).id_le x

/-- The paper's `L(x) = max {y : Φ_{D-1}(y) ≤ x}`. -/
def Lmax (D x : ℕ) : ℕ := Nat.findGreatest (fun y => Phi (D - 1) y ≤ x) x

theorem Lmax_le (D x : ℕ) : Lmax D x ≤ x := by
  exact Nat.findGreatest_le x

theorem Phi_Lmax_le {D : ℕ} (hD : 2 ≤ D) (x : ℕ) : Phi (D - 1) (Lmax D x) ≤ x := by
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 2 := ⟨D - 2, by omega⟩
  exact Nat.findGreatest_spec (P := fun y => Phi (E + 2 - 1) y ≤ x) (Nat.zero_le x)
    (by simp only [Phi_zero_right, Nat.zero_le])

theorem le_Lmax {D x y : ℕ} (hD : 2 ≤ D) (h : Phi (D - 1) y ≤ x) : y ≤ Lmax D x := by
  exact Nat.le_findGreatest ((le_Phi (by omega) y).trans h) h

theorem Lmax_eq_aux {E x y : ℕ} (hE : 1 ≤ E) (h1 : Phi E y ≤ x) (h2 : x < Phi E (y + 1)) :
    Lmax (E + 1) x = y := by
  have hD : 2 ≤ E + 1 := by omega
  have hle : y ≤ Lmax (E + 1) x := le_Lmax hD (by simpa only [Nat.add_sub_cancel] using h1)
  have hL := Phi_Lmax_le hD x
  simp only [Nat.add_sub_cancel] at hL
  refine le_antisymm ?_ hle
  by_contra hlt
  rw [not_le] at hlt
  have := (Phi_strictMono hE).monotone (by omega : y + 1 ≤ Lmax (E + 1) x)
  omega

/-- `L(x) = C(b - 1, D - 1) - c_⟨D-1⟩` for `x` in the band below `C(b, D)`, `c = C(b, D) - x`. -/
theorem Lmax_eq {D x b : ℕ} (hD : 2 ≤ D) (h1 : Nat.choose (b - 1) D < x)
    (h2 : x ≤ Nat.choose b D) :
    Lmax D x = Nat.choose (b - 1) (D - 1) - low (D - 1) (Nat.choose b D - x) := by
  have hx : 0 < x := by omega
  have hb : b ≠ 0 := by
    rintro rfl
    have : Nat.choose 0 D = 0 := Nat.choose_eq_zero_of_lt (by omega)
    omega
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have hP : Nat.choose (a + 1) (E + 1) = Nat.choose a E + Nat.choose a (E + 1) :=
    Nat.choose_succ_succ' a E
  generalize hc_def : Nat.choose (a + 1) (E + 1) - x = c
  have hc : c < Nat.choose a E := by omega
  have hE1 : 1 ≤ E := by omega
  rcases Nat.lt_or_ge E 2 with hE2 | hE2
  · obtain rfl : E = 1 := by omega
    simp only [Nat.reduceAdd, Nat.choose_one_right] at hP hc h1 h2 hc_def ⊢
    rw [low_one]
    split_ifs with h0
    · subst h0
      have h3 := Nat.choose_succ_succ' (a + 1) 1
      simp only [Nat.reduceAdd, Nat.choose_one_right] at h3
      apply Lmax_eq_aux (E := 1) le_rfl
      · rw [Phi_one, up_one, Nat.sub_zero]
        omega
      · rw [Phi_one, up_one, Nat.sub_zero]
        omega
    · apply Lmax_eq_aux (E := 1) le_rfl
      · rw [Phi_one, up_one, Nat.sub_add_cancel (by omega : 1 ≤ a)]
        omega
      · rw [Nat.sub_add_cancel (by omega : 1 ≤ a), Phi_one, up_one]
        omega
  · have haE : E ≤ a := by
      by_contra h
      rw [Nat.choose_eq_zero_of_lt (by omega)] at hc
      omega
    have hU := le_up_low (D := E - 1) (by omega) c
    rw [Nat.sub_add_cancel hE1] at hU
    have hlowc : low E c ≤ c := low_le_self E c
    apply Lmax_eq_aux hE1
    · by_cases hy : Nat.choose a E - low E c ≤ Nat.choose (a - 1) E
      · calc Phi E (Nat.choose a E - low E c) ≤ Phi E (Nat.choose (a - 1) E) :=
              (Phi_strictMono hE1).monotone hy
          _ = Nat.choose (a - 1 + 1) (E + 1) := Phi_choose hE1 _
          _ = Nat.choose a (E + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
          _ ≤ x := h1.le
      · have hB := Phi_band (D := E) (b := a) (x := Nat.choose a E - low E c) hE2
          (by omega) (by omega)
        rw [Nat.sub_sub_self (by omega : low E c ≤ Nat.choose a E)] at hB
        omega
    · rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0
        rw [low_zero_right, Nat.sub_zero]
        have h3 := (Phi_strictMono hE1) (by omega : Nat.choose a E < Nat.choose a E + 1)
        rw [Phi_choose hE1] at h3
        omega
      · have hl1 := low_pos hE1 h0
        have haE' : E + 1 ≤ a := by
          rcases Nat.lt_or_ge E a with h | h
          · omega
          · have : a = E := by omega
            subst this
            rw [Nat.choose_self] at hc
            omega
        have hl2 : low E c ≤ Nat.choose (a - 1) (E - 1) := by
          rw [← low_choose_sub_one hE1 haE']
          exact low_mono E (by omega)
        have hP2 : Nat.choose a E = Nat.choose (a - 1) (E - 1) + Nat.choose (a - 1) E := by
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          obtain ⟨F, rfl⟩ : ∃ F, E = F + 1 := ⟨E - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          exact Nat.choose_succ_succ' a' F
        have hB := Phi_band (D := E) (b := a) (x := Nat.choose a E - low E c + 1) hE2
          (by omega) (by omega)
        have h4 : Nat.choose a E - (Nat.choose a E - low E c + 1) = low E c - 1 := by omega
        rw [h4] at hB
        have h5 : ¬ c ≤ up (E - 1) (low E c - 1) := by
          rw [galois (D := E - 1) (by omega), Nat.sub_add_cancel hE1]
          omega
        omega

/-- **Lemma 4.2 (b).** `Φ_D(x) = x + Φ_D(x - L(x))` for `x ≥ 1`. -/
theorem Phi_fixed {D x : ℕ} (hD : 2 ≤ D) (hx : 0 < x) :
    Phi D x = x + Phi D (x - Lmax D x) := by
  have pascal : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      Nat.choose n k = Nat.choose (n - 1) (k - 1) + Nat.choose (n - 1) k := by
    intro n k hn hk
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.choose_succ_succ' n' k'
  obtain ⟨h1, h2⟩ := ctop_spec (D := D) (by omega) hx
  have hb := le_ctop (D := D) (by omega) hx
  generalize ctop D x = b at h1 h2 hb
  have hL := Lmax_eq hD h1 h2
  have hPx := Phi_band hD h1 h2
  rw [hL]
  have hlow := low_le_self (D - 1) (Nat.choose b D - x)
  have hpb := pascal b D (by omega) (by omega)
  rcases Nat.eq_or_lt_of_le hb with hbD | hbD
  · subst hbD
    have hc1 : Nat.choose D D = 1 := Nat.choose_self D
    have hc0 : Nat.choose (D - 1) D = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hc2 : Nat.choose (D - 1) (D - 1) = 1 := Nat.choose_self _
    have hc3 : Nat.choose (D + 1) (D + 1) = 1 := Nat.choose_self _
    have hx1 : x = 1 := by omega
    subst hx1
    rw [hc1, Nat.sub_self, low_zero_right, hc2]
    rw [hc1, hc3, Nat.sub_self, up_zero_right] at hPx
    rw [Nat.sub_self, Phi_zero_right]
    omega
  · set c := Nat.choose b D - x
    have hc_lt : c < Nat.choose (b - 1) (D - 1) := by omega
    have hs := S_lt_band (D := D - 1) (a := b - 1) (by omega) hc_lt
    have hSdef : S (D - 1) c = c - low (D - 1) c := rfl
    have hpb1 := pascal (b - 1) D (by omega) (by omega)
    have hpb2 := pascal (b + 1) (D + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hpb2
    have hz1 : Nat.choose (b - 1 - 1) D <
        x - (Nat.choose (b - 1) (D - 1) - low (D - 1) c) := by omega
    have hz2 : x - (Nat.choose (b - 1) (D - 1) - low (D - 1) c) ≤ Nat.choose (b - 1) D := by
      omega
    have hPz := Phi_band hD hz1 hz2
    have hzc : Nat.choose (b - 1) D - (x - (Nat.choose (b - 1) (D - 1) - low (D - 1) c)) =
        S (D - 1) c := by omega
    rw [hzc, Nat.sub_add_cancel (by omega : 1 ≤ b)] at hPz
    have hup := up_eq_add_up_S (D := D - 1) (by omega) c
    omega

/-- **Lemma 4.2 (c)**, inequality: `Φ_D(x) ≥ x^⟨D⟩`. -/
theorem up_le_Phi {D : ℕ} (hD : 1 ≤ D) (x : ℕ) : up D x ≤ Phi D x := by
  induction D, hD using Nat.le_induction generalizing x with
  | base => rw [Phi_one]
  | succ D hD ih =>
    induction x using Nat.strong_induction_on with
    | _ x ihx =>
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp
      have hD2 : 2 ≤ D + 1 := by omega
      have hL : Phi D (Lmax (D + 1) x) ≤ x := by
        have h := Phi_Lmax_le hD2 x
        rwa [Nat.add_sub_cancel] at h
      have hL2 : Lmax (D + 1) x ≤ low (D + 1) x := by
        have h1 : up D (Lmax (D + 1) x) ≤ x := (ih _).trans hL
        have h2 := low_mono (D + 1) h1
        rwa [low_up hD] at h2
      have hS : S (D + 1) x ≤ x - Lmax (D + 1) x := by
        simp only [S]
        omega
      have hSlt : S (D + 1) x < x := S_lt_self (by omega) hx
      rw [Phi_fixed hD2 hx, up_eq_add_up_S (by omega) x]
      have h3 := ihx _ hSlt
      have h4 := (Phi_strictMono (by omega : 1 ≤ D + 1)).monotone hS
      omega

end Macaulay

namespace NestedChains

open Macaulay

variable {α : Type*} [LinearOrder α]

theorem Phi_le_sum_prefix_aux {s : Finset α} {a : α} (hlt : ∀ x ∈ s, x < a) (e : α → ℕ)
    {D : ℕ}
    (he : ∀ θ ∈ insert a s, e θ ≤ Lmax D (∑ θ' ∈ (insert a s).filter (· ≤ θ), e θ')) :
    ∀ θ ∈ s, e θ ≤ Lmax D (∑ θ' ∈ s.filter (· ≤ θ), e θ') := fun θ hθ => by
  rw [← up_le_sum_prefix_aux hlt hθ]
  exact he θ (Finset.mem_insert_of_mem hθ)

/-- **Step 3 of Theorem 4.3**, arithmetic form: if `e θ ≤ L(X θ)` for the prefix sums
`X θ = ∑_{θ' ≤ θ} e θ'`, then `Φ_D(∑ e) ≤ ∑_θ X θ`. -/
theorem Phi_le_sum_prefix {D : ℕ} (hD : 2 ≤ D) (T : Finset α) (e : α → ℕ)
    (he : ∀ θ ∈ T, e θ ≤ Lmax D (∑ θ' ∈ T.filter (· ≤ θ), e θ')) :
    Phi D (∑ θ ∈ T, e θ) ≤ ∑ θ ∈ T, ∑ θ' ∈ T.filter (· ≤ θ), e θ' := by
  induction T using Finset.induction_on_max with
  | h0 => simp only [Finset.sum_empty, Phi_zero_right, le_refl]
  | step a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hea := he a (Finset.mem_insert_self a s)
    rw [up_le_sum_prefix_aux2 hlt] at hea
    rw [up_le_sum_prefix_aux4 hlt]
    rcases Nat.eq_zero_or_pos (∑ θ ∈ insert a s, e θ) with h0 | hpos
    · rw [h0, Phi_zero_right]
      exact Nat.zero_le _
    · rw [Phi_fixed hD hpos]
      refine Nat.add_le_add_left (((Phi_strictMono (by omega)).monotone ?_).trans
        (ih (Phi_le_sum_prefix_aux hlt e he))) _
      rw [Finset.sum_insert has] at hea ⊢
      omega

/-- **Theorem 4.3** for multichains: `h_A(D + 1) ≥ Φ_D(h_A(D))`. -/
theorem nested_complement (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) :
    Phi D (h A D) ≤ h A (D + 1) := by
  have key : ∀ n : ℕ, ∀ B : ℕ → Finset α, Monotone B →
      Phi (n + 1) (h B (n + 1)) ≤ h B (n + 2) := by
    intro n
    induction n with
    | zero =>
      intro B hB
      exact (Phi_one _).le.trans (nested_reverse_macaulay B hB 1 le_rfl)
    | succ m ih =>
      intro B hB
      have he : ∀ θ ∈ B (m + 1), ends B (m + 1) θ ≤
          Lmax (m + 1 + 1) (∑ θ' ∈ (B (m + 1)).filter (· ≤ θ), ends B (m + 1) θ') := by
        intro θ hθ
        apply le_Lmax (by omega)
        have hk := ih (trunc B θ) (trunc_mono hB θ)
        rw [← ends_succ_eq_h_trunc hθ, h_trunc_succ] at hk
        rw [Nat.add_sub_cancel]
        exact hk
      exact (Phi_le_sum_prefix (D := m + 1 + 1) (by omega) (B (m + 1)) (ends B (m + 1))
        he).trans (sum_prefix_le_h_succ hB (m + 1))
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  exact key n A hA

/-- **Theorem 4.3** for strict chains (Corollary 4.4): `h^<_A(D + 1) ≥ Φ_D(x) - x` with
`x = h^<_A(D)`. -/
theorem nested_complement_strict (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) :
    Phi D (hS A D) - hS A D ≤ hS A (D + 1) := by
  have key : ∀ n : ℕ, ∀ B : ℕ → Finset α, Monotone B →
      Phi (n + 1) (hS B (n + 1)) - hS B (n + 1) ≤ hS B (n + 2) := by
    intro n
    induction n with
    | zero =>
      intro B hB
      have h1 := nested_reverse_kk B hB 1 le_rfl
      have h2 := kk_add_self (D := 1) le_rfl (hS B 1)
      have h3 := Phi_one (hS B 1)
      change Phi 1 (hS B 1) - hS B 1 ≤ hS B (1 + 1)
      omega
    | succ m ih =>
      intro B hB
      have he : ∀ θ ∈ B (m + 1), endsS B (m + 1) θ ≤
          Lmax (m + 1 + 1) (∑ θ' ∈ (B (m + 1)).filter (· ≤ θ), endsS B (m + 1) θ') := by
        intro θ hθ
        apply le_Lmax (by omega)
        have hk := ih (truncLt B θ) (truncLt_mono hB θ)
        rw [← endsS_succ_eq_hS_truncLt hθ, hS_truncLt_succ] at hk
        have hle := le_Phi (D := m + 1) (by omega) (endsS B (m + 1) θ)
        rw [Nat.add_sub_cancel, endsS_le_low_prefix_aux hθ]
        omega
      have h1 := Phi_le_sum_prefix (D := m + 1 + 1) (by omega) (B (m + 1)) (endsS B (m + 1)) he
      have h2 := sum_strict_prefix_le_hS_succ hB (m + 1)
      have h3 : ∑ w ∈ B (m + 1), ∑ θ ∈ (B (m + 1)).filter (· ≤ w), endsS B (m + 1) θ =
          ∑ w ∈ B (m + 1), ∑ θ ∈ (B (m + 1)).filter (· < w), endsS B (m + 1) θ +
            ∑ w ∈ B (m + 1), endsS B (m + 1) w := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [endsS_le_low_prefix_aux hw, Nat.add_comm]
      have h5 : hS B (m + 1 + 1) = ∑ w ∈ B (m + 1), endsS B (m + 1) w := rfl
      rw [h5]
      omega
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  exact key n A hA

/-- Theorem 4.3 contains Theorem 3.1. -/
example (A : ℕ → Finset α) (hA : Monotone A) (D : ℕ) (hD : 1 ≤ D) :
    up D (h A D) ≤ h A (D + 1) :=
  (up_le_Phi hD _).trans (nested_complement A hA D hD)

end NestedChains

/-! ### Small checks -/

example : Macaulay.Phi 3 8 = 13 := by decide
example : Macaulay.Phi 2 7 = 14 := by decide

end CbsLean
