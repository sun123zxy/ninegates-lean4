import Mathlib
import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ}

def restrictLT (k : Fin (3 * n)) (c : Hand n) : Hand n :=
  fun i => if i < k then c i else 0

def restrictGT (k : Fin (3 * n)) (c : Hand n) : Hand n :=
  fun i => if k < i then c i else 0

@[simp]
lemma restrictLT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictLT k c i = if i < k then c i else 0 := rfl

@[simp]
lemma restrictGT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictGT k c i = if k < i then c i else 0 := rfl

private def restrictLTHom (k : Fin (3 * n)) : Hand n →+ Hand n where
  toFun := restrictLT k
  map_zero' := by ext; simp
  map_add' c d := by ext; simp; split <;> rfl

private def restrictGTHom (k : Fin (3 * n)) : Hand n →+ Hand n where
  toFun := restrictGT k
  map_zero' := by ext; simp
  map_add' c d := by ext; simp; split <;> rfl

@[simp]
private lemma restrictLTHom_apply (k : Fin (3 * n)) (c : Hand n) :
    restrictLTHom k c = restrictLT k c := rfl

@[simp]
private lemma restrictGTHom_apply (k : Fin (3 * n)) (c : Hand n) :
    restrictGTHom k c = restrictGT k c := rfl

private lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by
  ext x
  by_cases hx : x < k
  · simp [hx]
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact hx hi
    simp [hx, hxi]

private lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by
  ext x
  by_cases hx : x < k
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact hi hx
    simp [hx, hxi]
  · simp [hx]

private lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by
  ext x
  by_cases hx : k < x
  · simp [hx]
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact hx hi
    simp [hx, hxi]

private lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (single i) = 0 := by
  ext x
  by_cases hx : k < x
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact hi hx
    simp [hx, hxi]
  · simp [hx]

private lemma restrictLT_triplet_of_lt (k i : Fin (3 * n)) (a : ℕ) (hi : i < k) :
    restrictLT k (a • triplet i) = a • triplet i := by
  rw [← restrictLTHom_apply, triplet, map_nsmul, map_nsmul,
    restrictLTHom_apply, restrictLT_single_of_lt _ _ hi]

private lemma restrictLT_triplet_of_not_lt (k i : Fin (3 * n)) (a : ℕ)
    (hi : ¬i < k) : restrictLT k (a • triplet i) = 0 := by
  rw [← restrictLTHom_apply, triplet, map_nsmul, map_nsmul,
    restrictLTHom_apply, restrictLT_single_of_not_lt _ _ hi]
  simp

private lemma restrictGT_triplet_of_gt (k i : Fin (3 * n)) (a : ℕ) (hi : k < i) :
    restrictGT k (a • triplet i) = a • triplet i := by
  rw [← restrictGTHom_apply, triplet, map_nsmul, map_nsmul,
    restrictGTHom_apply, restrictGT_single_of_gt _ _ hi]

private lemma restrictGT_triplet_of_not_gt (k i : Fin (3 * n)) (a : ℕ)
    (hi : ¬k < i) : restrictGT k (a • triplet i) = 0 := by
  rw [← restrictGTHom_apply, triplet, map_nsmul, map_nsmul,
    restrictGTHom_apply, restrictGT_single_of_not_gt _ _ hi]
  simp

private lemma restrictLT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictLT k (sequence j) = sequence j := by
  rw [← restrictLTHom_apply, sequence, map_add, map_add]
  simp only [restrictLTHom_apply]
  have h₀ : (⟨j, by omega⟩ : Fin (3 * n)) < k := by
    change j.val < k.val
    omega
  have h₁ : (⟨j + 1, by omega⟩ : Fin (3 * n)) < k := by
    change j.val + 1 < k.val
    omega
  have h₂ : (⟨j + 2, by omega⟩ : Fin (3 * n)) < k := by
    change j.val + 2 < k.val
    omega
  rw [restrictLT_single_of_lt _ _ h₀, restrictLT_single_of_lt _ _ h₁,
    restrictLT_single_of_lt _ _ h₂]

private lemma restrictLT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictLT k (sequence j) = 0 := by
  rw [← restrictLTHom_apply, sequence, map_add, map_add]
  simp only [restrictLTHom_apply]
  have h₀ : ¬(⟨j, by omega⟩ : Fin (3 * n)) < k := by
    change ¬j.val < k.val
    omega
  have h₁ : ¬(⟨j + 1, by omega⟩ : Fin (3 * n)) < k := by
    change ¬j.val + 1 < k.val
    omega
  have h₂ : ¬(⟨j + 2, by omega⟩ : Fin (3 * n)) < k := by
    change ¬j.val + 2 < k.val
    omega
  rw [restrictLT_single_of_not_lt _ _ h₀,
    restrictLT_single_of_not_lt _ _ h₁,
    restrictLT_single_of_not_lt _ _ h₂]
  simp

private lemma restrictGT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictGT k (sequence j) = sequence j := by
  rw [← restrictGTHom_apply, sequence, map_add, map_add]
  simp only [restrictGTHom_apply]
  have h₀ : k < (⟨j, by omega⟩ : Fin (3 * n)) := by
    change k.val < j.val
    omega
  have h₁ : k < (⟨j + 1, by omega⟩ : Fin (3 * n)) := by
    change k.val < j.val + 1
    omega
  have h₂ : k < (⟨j + 2, by omega⟩ : Fin (3 * n)) := by
    change k.val < j.val + 2
    omega
  rw [restrictGT_single_of_gt _ _ h₀, restrictGT_single_of_gt _ _ h₁,
    restrictGT_single_of_gt _ _ h₂]

private lemma restrictGT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictGT k (sequence j) = 0 := by
  rw [← restrictGTHom_apply, sequence, map_add, map_add]
  simp only [restrictGTHom_apply]
  have h₀ : ¬k < (⟨j, by omega⟩ : Fin (3 * n)) := by
    change ¬k.val < j.val
    omega
  have h₁ : ¬k < (⟨j + 1, by omega⟩ : Fin (3 * n)) := by
    change ¬k.val < j.val + 1
    omega
  have h₂ : ¬k < (⟨j + 2, by omega⟩ : Fin (3 * n)) := by
    change ¬k.val < j.val + 2
    omega
  rw [restrictGT_single_of_not_gt _ _ h₀,
    restrictGT_single_of_not_gt _ _ h₁,
    restrictGT_single_of_not_gt _ _ h₂]
  simp

private lemma meldable_zero : Meldable (0 : Hand n) := by
  use 0, 0
  simp

private lemma meldable_nsmul {c : Hand n} (hc : Meldable c) (a : ℕ) :
    Meldable (a • c) := by
  induction a with
  | zero => simpa using (meldable_zero : Meldable (0 : Hand n))
  | succ a ih =>
      rw [succ_nsmul]
      exact Meldable.add ih hc

private lemma meldable_sum {ι : Type*} {s : Finset ι} {f : ι → Hand n}
    (hf : ∀ i ∈ s, Meldable (f i)) : Meldable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (meldable_zero : Meldable (0 : Hand n))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact Meldable.add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private def evalHom (k : Fin (3 * n)) : Hand n →+ ℕ where
  toFun c := c k
  map_zero' := zero_apply k
  map_add' c d := add_apply c d k

@[simp]
private lemma evalHom_apply (k : Fin (3 * n)) (c : Hand n) : evalHom k c = c k := rfl

theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : Fin (3 * n)) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  obtain ⟨t, r, h⟩ := hc
  have hcross (j : Fin (3 * n - 2)) (hleft : ¬j.val + 2 < k.val)
      (hright : ¬k.val < j.val) : r j = 0 := by
    have hseq : (show Hand n from Mahjong.Hand.sequence j) k = 1 := by
      change
        (show Hand n from
          single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
            single ⟨j + 2, by omega⟩) k = 1
      simp only [add_apply, single_apply]
      split_ifs with h₀ h₁ h₂ <;> simp_all only [Fin.ext_iff]
      all_goals omega
    have htotal :
        evalHom k
          (∑ i, t i • Mahjong.Hand.triplet i +
            ∑ x, r x • Mahjong.Hand.sequence x) = 0 := by
      rw [← h]
      exact hk
    simp only [map_add, map_sum, map_nsmul, evalHom_apply] at htotal
    have hseqsum : ∑ x, r x • (show Hand n from Mahjong.Hand.sequence x) k = 0 :=
      Nat.eq_zero_of_add_eq_zero_left htotal
    have hj : r j • (show Hand n from Mahjong.Hand.sequence j) k = 0 :=
      (Finset.sum_eq_zero_iff.mp hseqsum) j (Finset.mem_univ j)
    simp only [hseq, smul_eq_mul, mul_one] at hj
    exact hj
  have hleft_eq :
      restrictLT k c =
        ∑ i, restrictLT k (t i • Mahjong.Hand.triplet i) +
          ∑ j, restrictLT k (r j • Mahjong.Hand.sequence j) := by
    rw [h, ← restrictLTHom_apply, map_add, map_sum, map_sum]
    simp only [restrictLTHom_apply]
  have hright_eq :
      restrictGT k c =
        ∑ i, restrictGT k (t i • Mahjong.Hand.triplet i) +
          ∑ j, restrictGT k (r j • Mahjong.Hand.sequence j) := by
    rw [h, ← restrictGTHom_apply, map_add, map_sum, map_sum]
    simp only [restrictGTHom_apply]
  constructor
  · rw [hleft_eq]
    apply Meldable.add
    · apply meldable_sum
      intro i _
      by_cases hi : i < k
      · rw [restrictLT_triplet_of_lt _ _ _ hi]
        exact meldable_nsmul Meldable.triplet _
      · rw [restrictLT_triplet_of_not_lt _ _ _ hi]
        exact meldable_zero
    · apply meldable_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · rw [← restrictLTHom_apply, map_nsmul, restrictLTHom_apply,
          restrictLT_sequence_of_left _ _ hj]
        exact meldable_nsmul Meldable.sequence _
      · by_cases hj' : k.val < j.val
        · rw [← restrictLTHom_apply, map_nsmul, restrictLTHom_apply,
            restrictLT_sequence_of_right _ _ hj']
          exact meldable_zero
        · rw [hcross j hj hj']
          simp only [zero_nsmul]
          rw [← restrictLTHom_apply, map_zero]
          exact meldable_zero
  · rw [hright_eq]
    apply Meldable.add
    · apply meldable_sum
      intro i _
      by_cases hi : k < i
      · rw [restrictGT_triplet_of_gt _ _ _ hi]
        exact meldable_nsmul Meldable.triplet _
      · rw [restrictGT_triplet_of_not_gt _ _ _ hi]
        exact meldable_zero
    · apply meldable_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · rw [← restrictGTHom_apply, map_nsmul, restrictGTHom_apply,
          restrictGT_sequence_of_left _ _ hj]
        exact meldable_zero
      · by_cases hj' : k.val < j.val
        · rw [← restrictGTHom_apply, map_nsmul, restrictGTHom_apply,
            restrictGT_sequence_of_right _ _ hj']
          exact meldable_nsmul Meldable.sequence _
        · rw [hcross j hj hj']
          simp only [zero_nsmul]
          rw [← restrictGTHom_apply, map_zero]
          exact meldable_zero

private lemma restrictLT_pair_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (pair i) = pair i := by
  rw [← restrictLTHom_apply, pair, map_nsmul, restrictLTHom_apply,
    restrictLT_single_of_lt _ _ hi]

private lemma restrictLT_pair_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (pair i) = 0 := by
  rw [← restrictLTHom_apply, pair, map_nsmul, restrictLTHom_apply,
    restrictLT_single_of_not_lt _ _ hi]
  simp

private lemma restrictGT_pair_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (pair i) = pair i := by
  rw [← restrictGTHom_apply, pair, map_nsmul, restrictGTHom_apply,
    restrictGT_single_of_gt _ _ hi]

private lemma restrictGT_pair_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (pair i) = 0 := by
  rw [← restrictGTHom_apply, pair, map_nsmul, restrictGTHom_apply,
    restrictGT_single_of_not_gt _ _ hi]
  simp

private lemma restrictLT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n))
    (hi : i < k) :
    restrictLT k (c + single i) = restrictLT k c + single i := by
  rw [← restrictLTHom_apply, map_add, restrictLTHom_apply, restrictLTHom_apply,
    restrictLT_single_of_lt _ _ hi]

private lemma restrictGT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n))
    (hi : i < k) :
    restrictGT k (c + single i) = restrictGT k c := by
  rw [← restrictGTHom_apply, map_add, restrictGTHom_apply, restrictGTHom_apply,
    restrictGT_single_of_not_gt _ _ (not_lt_of_ge (le_of_lt hi))]
  simp

private lemma restrictLT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n))
    (hi : k < i) :
    restrictLT k (c + single i) = restrictLT k c := by
  rw [← restrictLTHom_apply, map_add, restrictLTHom_apply, restrictLTHom_apply,
    restrictLT_single_of_not_lt _ _ (not_lt_of_ge (le_of_lt hi))]
  simp

private lemma restrictGT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n))
    (hi : k < i) :
    restrictGT k (c + single i) = restrictGT k c + single i := by
  rw [← restrictGTHom_apply, map_add, restrictGTHom_apply, restrictGTHom_apply,
    restrictGT_single_of_gt _ _ hi]

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k = 0) :
    (size (restrictLT k w) % 3 = 2 ∧
      size (restrictGT k w) % 3 = 0 ∧ Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧
      size (restrictGT k w) % 3 = 2 ∧ Meldable (restrictLT k w)) := by
  obtain ⟨_, d, p, hd, hwd⟩ := hw
  have hzero : d k + pair p k = 0 := by
    rw [hwd] at hk
    exact hk
  have hdk : d k = 0 := Nat.eq_zero_of_add_eq_zero_right hzero
  have hpair : pair p k = 0 := Nat.eq_zero_of_add_eq_zero_left hzero
  have hpk : p ≠ k := by
    intro h
    subst p
    simp [pair] at hpair
  obtain ⟨hdLT, hdGT⟩ := hd.split_at_zero k hdk
  rcases lt_or_gt_of_ne hpk with hleft | hright
  · left
    have hLT : restrictLT k w = restrictLT k d + pair p := by
      rw [hwd]
      rw [← restrictLTHom_apply, map_add, restrictLTHom_apply,
        restrictLTHom_apply, restrictLT_pair_of_lt _ _ hleft]
    have hGT : restrictGT k w = restrictGT k d := by
      rw [hwd]
      rw [← restrictGTHom_apply, map_add, restrictGTHom_apply,
        restrictGTHom_apply,
        restrictGT_pair_of_not_gt _ _ (not_lt_of_ge (le_of_lt hleft))]
      simp
    rw [hLT, hGT]
    refine ⟨?_, hdGT.size_mod_three, hdGT⟩
    rw [size_add, size_pair]
    rw [Nat.add_mod, hdLT.size_mod_three]
  · right
    have hLT : restrictLT k w = restrictLT k d := by
      rw [hwd]
      rw [← restrictLTHom_apply, map_add, restrictLTHom_apply,
        restrictLTHom_apply,
        restrictLT_pair_of_not_lt _ _ (not_lt_of_ge (le_of_lt hright))]
      simp
    have hGT : restrictGT k w = restrictGT k d + pair p := by
      rw [hwd]
      rw [← restrictGTHom_apply, map_add, restrictGTHom_apply,
        restrictGTHom_apply, restrictGT_pair_of_gt _ _ hright]
    rw [hLT, hGT]
    refine ⟨hdLT.size_mod_three, ?_, hdLT⟩
    rw [size_add, size_pair]
    rw [Nat.add_mod, hdGT.size_mod_three]

variable (hn : 2 ≤ n)

include hn in
theorem interior_positive (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i := by
  intro k hk
  by_contra hpositive
  have hck : c k = 0 := by omega
  let first : Fin (3 * n) := ⟨0, by omega⟩
  let last : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hfirst : first < k := by
    change 0 < k.val
    exact hk.1
  have hlast : k < last := by
    change k.val < 3 * n - 1
    exact hk.2
  have hzero (i : Fin (3 * n)) (hi : i ≠ k) : (c + single i) k = 0 := by
    simp [hck, Ne.symm hi]
  have hfirst_zero : (c + single first) k = 0 :=
    hzero first (ne_of_lt hfirst)
  have hlast_zero : (c + single last) k = 0 :=
    hzero last (ne_of_gt hlast)
  have hfirst_sides := winning_sides_at_zero (hc first) k hfirst_zero
  have hlast_sides := winning_sides_at_zero (hc last) k hlast_zero
  rw [restrictLT_add_single_of_lt c k first hfirst,
    restrictGT_add_single_of_lt c k first hfirst,
    size_add, size_single] at hfirst_sides
  rw [restrictLT_add_single_of_gt c k last hlast,
    restrictGT_add_single_of_gt c k last hlast,
    size_add, size_single] at hlast_sides
  have hsizes :
      size (restrictLT k c) % 3 = 2 ∧ size (restrictGT k c) % 3 = 2 := by
    rcases hfirst_sides with hfirst_sides | hfirst_sides <;>
      rcases hlast_sides with hlast_sides | hlast_sides <;> omega
  have hleft_meldable (i : Fin (3 * n)) (hi : i < k) :
      Meldable (restrictLT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_lt hi)
    have hsides := winning_sides_at_zero (hc i) k hi_zero
    rw [restrictLT_add_single_of_lt c k i hi,
      restrictGT_add_single_of_lt c k i hi,
      size_add, size_single] at hsides
    rcases hsides with hsides | hsides
    · omega
    · simpa only [restrictLT_add_single_of_lt c k i hi] using hsides.2.2
  have hright_meldable (i : Fin (3 * n)) (hi : k < i) :
      Meldable (restrictGT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_gt hi)
    have hsides := winning_sides_at_zero (hc i) k hi_zero
    rw [restrictLT_add_single_of_gt c k i hi,
      restrictGT_add_single_of_gt c k i hi,
      size_add, size_single] at hsides
    rcases hsides with hsides | hsides
    · simpa only [restrictGT_add_single_of_gt c k i hi] using hsides.2.2
    · omega
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀ < k := by
      change 0 < k.val
      omega
    have hi₁ : i₁ < k := by
      change 1 < k.val
      omega
    have hsum₀ := (hleft_meldable i₀ hi₀).sum_mod_three
    have hsum₁ := (hleft_meldable i₁ hi₁).sum_mod_three
    rw [restrictLT_add_single_of_lt c k i₀ hi₀, sum_add, sum_single] at hsum₀
    rw [restrictLT_add_single_of_lt c k i₁ hi₁, sum_add, sum_single] at hsum₁
    change (sum (restrictLT k c) + 0) % 3 = 0 at hsum₀
    change (sum (restrictLT k c) + 1) % 3 = 0 at hsum₁
    omega
  · have hkval : k.val = 1 := by omega
    let i₂ : Fin (3 * n) :=
      ⟨2, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    let i₃ : Fin (3 * n) :=
      ⟨3, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    have hi₂ : k < i₂ := by
      change k.val < 2
      omega
    have hi₃ : k < i₃ := by
      change k.val < 3
      omega
    have hsum₂ := (hright_meldable i₂ hi₂).sum_mod_three
    have hsum₃ := (hright_meldable i₃ hi₃).sum_mod_three
    rw [restrictGT_add_single_of_gt c k i₂ hi₂, sum_add, sum_single] at hsum₂
    rw [restrictGT_add_single_of_gt c k i₃ hi₃, sum_add, sum_single] at hsum₃
    change (sum (restrictGT k c) + 2) % 3 = 0 at hsum₂
    change (sum (restrictGT k c) + 3) % 3 = 0 at hsum₃
    omega

end Mahjong.Hand
