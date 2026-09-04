import CbsLean.CbMaximality
import CbsLean.VWNumerator

/-!
# Labels, rooms and the identification `shell w l = #labels`  (W1 plan, item A1)

Companion to `W1_Proof_Note_v0_1.md` §3b (branching formulation) and §3d.

## Conventions
* Width lists and digit lists are stored **in reverse order** (deepest letter first), because
  `digitBox` (in `VWNumerator.lean`) builds digit vectors by `cons` at the head.  A VW label
  `(c₁, …, c_m)` for widths `(k₁, …, k_m)` is the list `[c_m, …, c₁]` with widths `[k_m, …, k₁]`.
* `admRev K cs` is the width-normalized monotonicity `c_j * k_{j+1} ≤ c_{j+1} * k_j` on adjacent
  entries, and `vwRev K = (digitBox K).filter admRev` is the VW label set `L(K)` of [VW] §2.
* `roomCount cs k k'` is the number of admissible next letters of a label `cs` whose last width is
  `k`, when the next width is `k'`; `roomMS K k'` is the multiset of these rooms over `vwRev K`.

## Main results
* `card_heads`: `roomCount = chainMap k k' (k - c)` (the paper's `⌊(k-c) k'/k⌋`).
* `roomMS_cons`: `roomMS (k' :: K) k'' = Phi (chainMap k' k'') (roomMS K k')` (Lemma B bookkeeping).
* `rooms_eq_roomMS`, `shell_eq_card`: `rooms w l` of `CbMaximality.lean` is the room multiset of
  the actual label set with widths `(1, w 0, …, w (l-1))`, and `shell w l` is the number of labels
  of length `l + 2` with widths `(1, w 0, …, w l)`.
-/

open Finset
open scoped BigOperators

namespace CbsLean
namespace CbMax

/-- Width-normalized monotonicity on reversed lists (widths, digits). -/
def admRev : List ℕ → List ℕ → Bool
  | k' :: k :: ks, c' :: c :: cs => decide (c * k' ≤ c' * k) && admRev (k :: ks) (c :: cs)
  | [_], [_] => true
  | _, _ => false

/-- The VW label set for a (reversed) width list. -/
def vwRev (K : List ℕ) : Finset (List ℕ) := (digitBox K).filter (fun cs => admRev K cs = true)

/-- Admissible next letters of a label whose head (deepest letter) is `c` with last width `k`,
when the next width is `k'`: `{c' < k' : c * k' ≤ c' * k}`. -/
def heads (c k k' : ℕ) : Finset ℕ := (Finset.range k').filter (fun c' => c * k' ≤ c' * k)

def roomCount (cs : List ℕ) (k k' : ℕ) : ℕ := (heads (cs.headD 0) k k').card

/-- Rooms of all labels with (reversed) widths `K` with respect to the next width `k'`. -/
def roomMS (K : List ℕ) (k' : ℕ) : Multiset ℕ :=
  (vwRev K).val.map (fun cs => roomCount cs (K.headD 1) k')

/-! ### The arithmetic of one room -/

theorem heads_eq_Ico (c k k' : ℕ) (hk : 0 < k) :
    heads c k k' = Finset.Ico ((c * k' + k - 1) / k) k' := by
  ext c'
  simp only [heads, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  have hcomm : c' * k = k * c' := Nat.mul_comm _ _
  have hsub : c * k' + k - 1 + 1 = c * k' + k := Nat.sub_add_cancel (by omega)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [Nat.div_le_iff_le_mul_add_pred hk]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [Nat.div_le_iff_le_mul_add_pred hk] at h1
    omega

theorem ceil_le_width (c k k' : ℕ) (hk : 0 < k) (hc : c < k) : (c * k' + k - 1) / k ≤ k' := by
  rw [Nat.div_le_iff_le_mul_add_pred hk]
  have : c * k' ≤ (k - 1) * k' := Nat.mul_le_mul_right k' (by omega)
  have h2 : (k - 1) * k' + k' = k * k' := by
    rw [Nat.sub_mul, one_mul]
    have : k' ≤ k * k' := Nat.le_mul_of_pos_left k' hk
    omega
  have h3 : k' * k = k * k' := Nat.mul_comm _ _
  omega

/-- `#heads = ⌊(k - c) k' / k⌋ = chainMap k k' (k - c)`. -/
theorem card_heads (c k k' : ℕ) (hk : 0 < k) (hc : c < k) :
    (heads c k k').card = chainMap k k' (k - c) := by
  rw [heads_eq_Ico c k k' hk, Nat.card_Ico]
  unfold chainMap
  set e := (c * k' + k - 1) / k with he
  have hle : e ≤ k' := ceil_le_width c k k' hk hc
  have hdm := Nat.div_add_mod (c * k' + k - 1) k
  have hmod := Nat.mod_lt (c * k' + k - 1) hk
  rw [← he] at hdm
  have hsub : c * k' + k - 1 + 1 = c * k' + k := Nat.sub_add_cancel (by omega)
  have h1 : k * e ≤ c * k' + k - 1 := by omega
  have h2 : c * k' + k - 1 < k * e + k := by omega
  symm
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, Nat.sub_mul]
    have hkk : k' * k = k * k' := Nat.mul_comm _ _
    have hek : e * k = k * e := Nat.mul_comm _ _
    have hck : c * k' ≤ k * k' := Nat.mul_le_mul_right k' (le_of_lt hc)
    have hek2 : k * e ≤ k * k' := Nat.mul_le_mul_left k hle
    omega
  · rw [Nat.sub_mul, Nat.succ_mul, Nat.sub_mul]
    have hkk : k' * k = k * k' := Nat.mul_comm _ _
    have hek : e * k = k * e := Nat.mul_comm _ _
    have hck : c * k' ≤ k * k' := Nat.mul_le_mul_right k' (le_of_lt hc)
    have hek2 : k * e ≤ k * k' := Nat.mul_le_mul_left k hle
    omega

theorem roomCount_cons (c' : ℕ) (cs : List ℕ) (k' k'' : ℕ) (hk' : 0 < k') (hc' : c' < k') :
    roomCount (c' :: cs) k' k'' = chainMap k' k'' (k' - c') := by
  unfold roomCount
  simp only [List.headD_cons]
  exact card_heads c' k' k'' hk' hc'

/-- Reflecting the interval of heads onto `{1, …, r}`: the rooms of the children of a label with
room `r` are exactly the chain `{chainMap k' k'' j : 1 ≤ j ≤ r}`. -/
theorem heads_val_map_reflect (c k k' k'' : ℕ) (hk : 0 < k) (hc : c < k) :
    (heads c k k').val.map (fun c' => chainMap k' k'' (k' - c'))
      = (Multiset.range (chainMap k k' (k - c))).map (fun i => chainMap k' k'' (i + 1)) := by
  rw [← card_heads c k k' hk hc, heads_eq_Ico c k k' hk, Nat.card_Ico]
  have hle : (c * k' + k - 1) / k ≤ k' := ceil_le_width c k k' hk hc
  generalize hE : (c * k' + k - 1) / k = e at hle ⊢
  have hIco : (Finset.Ico e k').val = (Multiset.range (k' - e)).map (fun i => k' - 1 - i) := by
    apply (Multiset.Nodup.ext (Finset.Ico e k').nodup ?_).mpr
    · intro x
      simp only [Finset.mem_val, Finset.mem_Ico, Multiset.mem_map, Multiset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨k' - 1 - x, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    · apply Multiset.Nodup.map_on _ (Multiset.nodup_range _)
      intro a ha b hb hab
      simp only [Multiset.mem_range] at ha hb
      omega
  rw [hIco, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  simp only [Multiset.mem_range] at hi
  simp only [Function.comp]
  congr 1
  omega

/-! ### Membership in `digitBox` and `vwRev` -/

theorem mem_digitBox_cons (k : ℕ) (ks : List ℕ) (x : List ℕ) :
    x ∈ digitBox (k :: ks) ↔ ∃ c cs, c < k ∧ cs ∈ digitBox ks ∧ x = c :: cs := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hp' := Finset.mem_product.mp hp
    exact ⟨p.1, p.2, Finset.mem_range.mp hp'.1, hp'.2, rfl⟩
  · rintro ⟨c, cs, hc, hcs, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨(c, cs), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hc, hcs⟩, rfl⟩

theorem mem_digitBox_nil (x : List ℕ) : x ∈ digitBox [] ↔ x = [] := by
  simp [digitBox]

theorem admRev_cons_cons (k' k : ℕ) (ks : List ℕ) (c' c : ℕ) (cs : List ℕ) :
    admRev (k' :: k :: ks) (c' :: c :: cs) = true ↔
      c * k' ≤ c' * k ∧ admRev (k :: ks) (c :: cs) = true := by
  simp [admRev]

/-- Every label at a level `k :: ks` starts with a digit `< k`. -/
theorem headD_lt_of_mem_vwRev (k : ℕ) (ks : List ℕ) (cs : List ℕ) (h : cs ∈ vwRev (k :: ks)) :
    cs.headD 0 < k := by
  unfold vwRev at h
  have hbox := (Finset.mem_filter.mp h).1
  rw [mem_digitBox_cons] at hbox
  obtain ⟨c, cs', hc, _, rfl⟩ := hbox
  simpa using hc

/-- Extension step for the label set (`K` nonempty). -/
theorem mem_vwRev_cons (k' k : ℕ) (ks : List ℕ) (x : List ℕ) :
    x ∈ vwRev (k' :: k :: ks) ↔
      ∃ c' cs, cs ∈ vwRev (k :: ks) ∧ c' ∈ heads (cs.headD 0) k k' ∧ x = c' :: cs := by
  unfold vwRev
  simp only [Finset.mem_filter, heads, Finset.mem_range]
  constructor
  · rintro ⟨hbox, hadm⟩
    rw [mem_digitBox_cons] at hbox
    obtain ⟨c', cs, hc', hcs, rfl⟩ := hbox
    rw [mem_digitBox_cons] at hcs
    obtain ⟨c, cs', hc, hcs', rfl⟩ := hcs
    rw [admRev_cons_cons] at hadm
    refine ⟨c', c :: cs', ⟨?_, hadm.2⟩, ⟨hc', ?_⟩, rfl⟩
    · rw [mem_digitBox_cons]
      exact ⟨c, cs', hc, hcs', rfl⟩
    · simpa using hadm.1
  · rintro ⟨c', cs, ⟨hbox, hadm⟩, ⟨hc', hle⟩, rfl⟩
    rw [mem_digitBox_cons] at hbox
    obtain ⟨c, cs', hc, hcs', rfl⟩ := hbox
    refine ⟨?_, ?_⟩
    · rw [mem_digitBox_cons]
      refine ⟨c', c :: cs', hc', ?_, rfl⟩
      rw [mem_digitBox_cons]
      exact ⟨c, cs', hc, hcs', rfl⟩
    · rw [admRev_cons_cons]
      exact ⟨by simpa using hle, hadm⟩

/-- The label multiset at level `k' :: K` is the disjoint union over labels `cs` at level `K`
of the extensions `c' :: cs`, `c' ∈ heads`. -/
theorem vwRev_cons_val (k' k : ℕ) (ks : List ℕ) :
    (vwRev (k' :: k :: ks)).val =
      (vwRev (k :: ks)).val.bind
        (fun cs => (heads (cs.headD 0) k k').val.map (fun c' => c' :: cs)) := by
  have hnd : ((vwRev (k :: ks)).val.bind
      (fun cs => (heads (cs.headD 0) k k').val.map (fun c' => c' :: cs))).Nodup := by
    have h1 : ((vwRev (k :: ks)).val.sigma (fun cs => (heads (cs.headD 0) k k').val)).Nodup :=
      Multiset.Nodup.sigma (vwRev _).nodup (fun cs => (heads _ _ _).nodup)
    have hinj : Function.Injective (fun x : (Σ _ : List ℕ, ℕ) => x.2 :: x.1) := by
      intro a b hab
      simp only [List.cons.injEq] at hab
      exact Sigma.ext hab.2 (heq_of_eq hab.1)
    have h2 := Multiset.Nodup.map hinj h1
    have h3 : ((vwRev (k :: ks)).val.sigma (fun cs => (heads (cs.headD 0) k k').val)).map
        (fun x : (Σ _ : List ℕ, ℕ) => x.2 :: x.1)
        = (vwRev (k :: ks)).val.bind
          (fun cs => (heads (cs.headD 0) k k').val.map (fun c' => c' :: cs)) := by
      unfold Multiset.sigma
      rw [Multiset.map_bind]
      apply Multiset.bind_congr
      intro cs _
      rw [Multiset.map_map]
      rfl
    rw [h3] at h2
    exact h2
  rw [Multiset.Nodup.ext (vwRev _).nodup hnd]
  intro x
  rw [Multiset.mem_bind]
  simp only [Multiset.mem_map, Finset.mem_val]
  rw [mem_vwRev_cons]
  constructor
  · rintro ⟨c', cs, hcs, hc', rfl⟩
    exact ⟨cs, hcs, c', hc', rfl⟩
  · rintro ⟨cs, hcs, c', hc', rfl⟩
    exact ⟨c', cs, hcs, hc', rfl⟩

/-! ### The room multisets follow the branching recursion -/

/-- **Lemma B (bookkeeping).** `roomMS (k' :: K) k'' = Phi (chainMap k' k'') (roomMS K k')`. -/
theorem roomMS_cons (k'' k' k : ℕ) (ks : List ℕ) (hk : 0 < k) (hk' : 0 < k') :
    roomMS (k' :: k :: ks) k'' = Phi (chainMap k' k'') (roomMS (k :: ks) k') := by
  unfold roomMS Phi
  simp only [List.headD_cons]
  rw [vwRev_cons_val, Multiset.map_bind, Multiset.bind_map]
  apply Multiset.bind_congr
  intro cs hcs
  have hc : cs.headD 0 < k := headD_lt_of_mem_vwRev k ks cs (Finset.mem_val.mp hcs)
  rw [Multiset.map_map]
  have hleft : (heads (cs.headD 0) k k').val.map
        ((fun cs' => roomCount cs' k' k'') ∘ (fun c' => c' :: cs))
      = (heads (cs.headD 0) k k').val.map (fun c' => chainMap k' k'' (k' - c')) := by
    apply Multiset.map_congr rfl
    intro c' hc'
    have hc'lt : c' < k' := by
      have := Finset.mem_val.mp hc'
      simp only [heads, Finset.mem_filter, Finset.mem_range] at this
      exact this.1
    simp only [Function.comp]
    exact roomCount_cons c' cs k' k'' hk' hc'lt
  rw [hleft, heads_val_map_reflect (cs.headD 0) k k' k'' hk hc]
  unfold roomCount
  rw [card_heads (cs.headD 0) k k' hk hc]

/-! ### Identification with `rooms` and `shell` of `CbMaximality.lean` -/

/-- Reversed width list `[w (l-1), …, w 0, 1]` (paper widths `(1, k₂, …, k_{l+1})`). -/
def widthsRev (w : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [1]
  | l + 1 => w l :: widthsRev w l

theorem widthsRev_cons (w : ℕ → ℕ) (l : ℕ) : ∃ k ks, widthsRev w l = k :: ks := by
  cases l with
  | zero => exact ⟨1, [], rfl⟩
  | succ l => exact ⟨w l, widthsRev w l, rfl⟩

theorem widthsRev_headD_pos (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (l : ℕ) :
    0 < (widthsRev w l).headD 1 := by
  cases l with
  | zero => simp [widthsRev]
  | succ l => simpa [widthsRev] using hpos l

theorem vwRev_one : vwRev [1] = {[0]} := by
  decide

theorem roomMS_base (k' : ℕ) : roomMS [1] k' = {k'} := by
  unfold roomMS
  rw [vwRev_one]
  simp only [Finset.singleton_val, Multiset.map_singleton, List.headD_cons]
  unfold roomCount heads
  simp

/-- `rooms w l` is the room multiset of the actual label set with widths `(1, w 0, …, w (l-1))`,
with respect to the next width `w l`. -/
theorem rooms_eq_roomMS (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) :
    ∀ l, rooms w l = roomMS (widthsRev w l) (w l)
  | 0 => by
    simp only [rooms, widthsRev]
    rw [roomMS_base]
  | l + 1 => by
    rw [rooms, rooms_eq_roomMS w hpos l]
    obtain ⟨k, ks, hk⟩ := widthsRev_cons w l
    have hkpos : 0 < k := by
      have := widthsRev_headD_pos w hpos l
      rw [hk] at this
      simpa using this
    have hnext : widthsRev w (l + 1) = w l :: widthsRev w l := rfl
    rw [hnext, hk, roomMS_cons (w (l + 1)) (w l) k ks hkpos (hpos l)]

/-- **A1.** `shell w l` is the number of VW labels of length `l + 2` with widths
`(1, w 0, …, w l)`, i.e. the paper's `g_{l+2}(K)`. -/
theorem shell_eq_card (w : ℕ → ℕ) (hpos : ∀ l, 0 < w l) (l : ℕ) :
    shell w l = (vwRev (widthsRev w (l + 1))).card := by
  unfold shell
  rw [rooms_eq_roomMS w hpos l]
  obtain ⟨k, ks, hk⟩ := widthsRev_cons w l
  have hnext : widthsRev w (l + 1) = w l :: widthsRev w l := rfl
  rw [hnext, hk, Finset.card_def, vwRev_cons_val, Multiset.card_bind]
  unfold roomMS
  simp only [List.headD_cons]
  congr 1
  apply Multiset.map_congr rfl
  intro cs _
  simp only [Function.comp, Multiset.card_map]
  rfl

end CbMax
end CbsLean
