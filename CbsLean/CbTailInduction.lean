import CbsLean.CbMaximality

/-!
# Lemma C by tail induction (a second proof of Theorem 5)

`ppred_succ_of_lam` in `CbMaximality.lean` proves `Ppred (l+1) (Phi c Y)` from `Lam l Y`
(Lemma C of the W1 note), which in turn needs Lemma A (`lam_of_ppred`) and, for the base level,
Lemma D (`ppred_one_of_distinct`).  This file gives a direct proof of

  `Ppred l Y → Ppred (l+1) (Phi c Y)`

by induction on the shift `t` of the target, with two cases at each step and no drop/sign-change
argument:

* the identity `N (Phi c Y) (u₀+t+1) = E Y (J c (u₀+t))` (`N_Phi`) and Pascal
  `shellCb (l+1) n = shellCb (l+1) (n-1) + shellCb l n`;
* **Case A** `E Y i ≤ shellCb l n`: the induction hypothesis alone suffices;
* **Case B** `E Y i > shellCb l n`: `n ≤ kappa l (E Y i)`, the shifted invariant
  `Wpred l (shift Y i)` and the hockey stick give `shellCb (l+1) (n-1) ≤ E (Phi id Y) (i+1)`,
  and the reduction `E (Phi id Y) (J c v) ≤ E (Phi c Y) v` (`E_phi_id_J_le_E_phi`, from
  `c k - v ≥ k - J c v`) transports this to `Phi c Y`.

Consequently `Ppred l (rooms w l)` holds for **every** level `l ≥ 0` (`ppred_rooms_all`),
which re-derives `ppred_rooms` (Theorem 5) without Lemmas A, C, D of the original route.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

section tail_induction

variable {c : ℕ → ℕ}

/-- For strictly monotone `c : ℕ → ℕ`: `c a + (b - a) ≤ c b` whenever `a ≤ b`. -/
theorem strictMono_add_sub_le (hc : StrictMono c) (a b : ℕ) (hab : a ≤ b) :
    c a + (b - a) ≤ c b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have := hc (show b < b + 1 by omega)
    omega

/-- `J c` increases by at most one per unit. -/
theorem J_succ_le (hc : StrictMono c) (hc0 : c 0 = 0) (v : ℕ) : J c (v + 1) ≤ J c v + 1 := by
  by_cases h : ∃ j, c j = v + 1
  · obtain ⟨j, hj⟩ := h
    have := J_of_eq hc hc0 j v hj
    omega
  · push_neg at h
    rw [J_succ_of_not_mem hc hc0 v h]
    omega

/-- `v < c (J c v + 1)`. -/
theorem lt_c_J_succ (hc : StrictMono c) (hc0 : c 0 = 0) (v : ℕ) : v < c (J c v + 1) :=
  ((J_eq_iff hc hc0 v (J c v)).1 rfl).2

/-- **Reduction to the identity chain.**  `E (Phi id Y) (J c v) ≤ E (Phi c Y) v`: each cell
`(y, i)` with `i + 1 > J c v` satisfies `c (i+1) - v ≥ i + 1 - J c v`. -/
theorem E_phi_id_J_le_E_phi (hc : StrictMono c) (hc0 : c 0 = 0) (Y : Multiset ℕ) (v : ℕ) :
    E (Phi id Y) (J c v) ≤ E (Phi c Y) v := by
  unfold E Phi
  rw [Multiset.map_bind, Multiset.map_bind, Multiset.sum_bind, Multiset.sum_bind]
  apply Multiset.sum_map_le_sum_map
  intro y _
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.sum_map_le_sum_map
  intro i _
  simp only [Function.comp, id]
  rcases Nat.lt_or_ge (J c v) (i + 1) with h | h
  · have h1 := strictMono_add_sub_le hc (J c v + 1) (i + 1) (by omega)
    have h2 := lt_c_J_succ hc hc0 v
    omega
  · rw [Nat.sub_eq_zero_of_le h]
    exact Nat.zero_le _

/-- Partial tail sums of `E Y` are bounded by `E (Phi id Y)`:
`∑_{s<t} E Y (w+s) ≤ E (Phi id Y) w`. -/
theorem sum_E_add_le_E_phi_id (Y : Multiset ℕ) (w t : ℕ) :
    ∑ s ∈ range t, E Y (w + s) ≤ E (Phi id Y) w := by
  have h := E_add_eq (Phi id Y) w t
  have hN : ∀ s, N (Phi id Y) (w + s + 1) = E Y (w + s) := by
    intro s
    rw [N_Phi strictMono_id rfl, J_id]
  have hsum : ∑ s ∈ range t, E Y (w + s) = ∑ s ∈ range t, N (Phi id Y) (w + s + 1) :=
    Finset.sum_congr rfl (fun s _ => (hN s).symm)
  rw [hsum]
  omega

/-- **Hockey stick from the shifted invariant.**  `Wpred l (shift Y i)` gives
`shellCb (l+1) (κ - 1) ≤ E (Phi id Y) (i+1)` with `κ = kappa l (E Y i)`. -/
theorem shellCb_succ_pred_le_E_phi_id_succ (l : ℕ) (Y : Multiset ℕ) (i : ℕ)
    (hW : Wpred l (shift Y i)) :
    shellCb (l + 1) (kappa l (E Y i) - 1) ≤ E (Phi id Y) (i + 1) := by
  have hW' : ∀ s, shellCb l (kappa l (E Y i) - s) ≤ E Y (i + s) := by
    intro s
    have := hW s
    rwa [E_shift, sum_shift] at this
  have h1 := shellCb_succ_sub_eq l (kappa l (E Y i) - 1) (kappa l (E Y i) - 1)
  rw [Nat.sub_self, shellCb_zero, zero_add] at h1
  rw [h1]
  calc ∑ s ∈ range (kappa l (E Y i) - 1), shellCb l (kappa l (E Y i) - 1 - s)
      ≤ ∑ s ∈ range (kappa l (E Y i) - 1), E Y (i + 1 + s) := by
        apply Finset.sum_le_sum
        intro s _
        have := hW' (1 + s)
        have e1 : kappa l (E Y i) - 1 - s = kappa l (E Y i) - (1 + s) := by omega
        have e2 : i + (1 + s) = i + 1 + s := by omega
        rw [e1, ← e2]
        exact this
    _ ≤ E (Phi id Y) (i + 1) := sum_E_add_le_E_phi_id Y (i + 1) _

/-- **Lemma C by tail induction.**  `Ppred l Y → Ppred (l+1) (Phi c Y)`. -/
theorem ppred_succ_of_ppred (hc : StrictMono c) (hc0 : c 0 = 0) (l : ℕ) (Y : Multiset ℕ)
    (hP : Ppred l Y) : Ppred (l + 1) (Phi c Y) := by
  intro u₀ t
  rw [E_shift, sum_shift]
  induction t with
  | zero =>
    simp only [Nat.sub_zero, Nat.add_zero]
    exact shellCb_kappa_le (l + 1) _
  | succ t ih =>
    rcases Nat.eq_zero_or_pos (kappa (l + 1) (E (Phi c Y) u₀) - t) with h0 | hpos
    · have : kappa (l + 1) (E (Phi c Y) u₀) - (t + 1) = 0 := by omega
      rw [this, shellCb_zero]
      exact Nat.zero_le _
    · have hn1 : kappa (l + 1) (E (Phi c Y) u₀) - (t + 1) =
          kappa (l + 1) (E (Phi c Y) u₀) - t - 1 := by omega
      rw [hn1]
      have hE : E (Phi c Y) (u₀ + t) = E (Phi c Y) (u₀ + t + 1) + E Y (J c (u₀ + t)) := by
        rw [E_succ (Phi c Y) (u₀ + t), N_Phi hc hc0]
      have hPas : shellCb (l + 1) (kappa (l + 1) (E (Phi c Y) u₀) - t) =
          shellCb (l + 1) (kappa (l + 1) (E (Phi c Y) u₀) - t - 1) +
            shellCb l (kappa (l + 1) (E (Phi c Y) u₀) - t) := by
        have := shellCb_succ_succ l (kappa (l + 1) (E (Phi c Y) u₀) - t - 1)
        rw [show kappa (l + 1) (E (Phi c Y) u₀) - t - 1 + 1 =
            kappa (l + 1) (E (Phi c Y) u₀) - t by omega] at this
        exact this
      have hadd : u₀ + (t + 1) = u₀ + t + 1 := by omega
      rw [hadd]
      rcases Nat.lt_or_ge (shellCb l (kappa (l + 1) (E (Phi c Y) u₀) - t)) (E Y (J c (u₀ + t)))
        with hB | hA
      · -- Case B: use the level-`l` invariant at shift `J c (u₀ + t)`
        have hk : kappa (l + 1) (E (Phi c Y) u₀) - t ≤ kappa l (E Y (J c (u₀ + t))) :=
          le_kappa_of l _ _ (le_of_lt hB)
        have h1 := shellCb_succ_pred_le_E_phi_id_succ l Y (J c (u₀ + t)) (hP _)
        have h2 : shellCb (l + 1) (kappa (l + 1) (E (Phi c Y) u₀) - t - 1) ≤
            shellCb (l + 1) (kappa l (E Y (J c (u₀ + t))) - 1) :=
          shellCb_mono (l + 1) (by omega)
        have h3 : E (Phi id Y) (J c (u₀ + t) + 1) ≤ E (Phi id Y) (J c (u₀ + t + 1)) :=
          E_antitone _ (J_succ_le hc hc0 (u₀ + t))
        have h4 := E_phi_id_J_le_E_phi hc hc0 Y (u₀ + t + 1)
        omega
      · -- Case A: the current level-`l` tail is within the cb budget
        omega

end tail_induction

/-- **Theorem 5 by tail induction.**  `Ppred l (rooms w l)` at every level `l ≥ 0`; the case
`l + 1` is `ppred_rooms`, now obtained without Lemmas A, C, D. -/
theorem ppred_rooms_all (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (hmono : Monotone w) :
    ∀ l, Ppred l (rooms w l) := by
  intro l
  induction l with
  | zero =>
    intro u
    have h : shift {w 0} u = {w 0 - u} := by simp [shift]
    change Wpred 0 (shift {w 0} u)
    rw [h]
    exact wpred_zero_singleton _
  | succ l ih =>
    change Ppred (l + 1) (Phi (chainMap (w l) (w (l + 1))) (rooms w l))
    exact ppred_succ_of_ppred (chainMap_strictMono (hpos l) (hmono (Nat.le_succ l)))
      (chainMap_zero _ _) l _ ih

end CbMax
end CbsLean
