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

private lemma restrictLT_add (k : Fin (3 * n)) (c d : Hand n) :
    restrictLT k (c + d) = restrictLT k c + restrictLT k d := by
  rw [← restrictLTHom_apply, map_add, restrictLTHom_apply, restrictLTHom_apply]

private lemma restrictGT_add (k : Fin (3 * n)) (c d : Hand n) :
    restrictGT k (c + d) = restrictGT k c + restrictGT k d := by
  rw [← restrictGTHom_apply, map_add, restrictGTHom_apply, restrictGTHom_apply]

private lemma restrictLT_nsmul (k : Fin (3 * n)) (a : ℕ) (c : Hand n) :
    restrictLT k (a • c) = a • restrictLT k c := by
  rw [← restrictLTHom_apply, map_nsmul, restrictLTHom_apply]

private lemma restrictGT_nsmul (k : Fin (3 * n)) (a : ℕ) (c : Hand n) :
    restrictGT k (a • c) = a • restrictGT k c := by
  rw [← restrictGTHom_apply, map_nsmul, restrictGTHom_apply]

private lemma restrictLT_zero (k : Fin (3 * n)) :
    restrictLT k (0 : Hand n) = 0 := by
  rw [← restrictLTHom_apply, map_zero]

private lemma restrictGT_zero (k : Fin (3 * n)) :
    restrictGT k (0 : Hand n) = 0 := by
  rw [← restrictGTHom_apply, map_zero]

private lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

private lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

private lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

private lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (single i) = 0 := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

private lemma restrictLT_triplet_of_lt (k i : Fin (3 * n)) (a : ℕ) (hi : i < k) :
    restrictLT k (a • triplet i) = a • triplet i := by
  rw [restrictLT_nsmul, triplet, restrictLT_nsmul,
    restrictLT_single_of_lt _ _ hi]

private lemma restrictLT_triplet_of_not_lt (k i : Fin (3 * n)) (a : ℕ)
    (hi : ¬i < k) : restrictLT k (a • triplet i) = 0 := by
  simp only [restrictLT_nsmul, triplet, restrictLT_single_of_not_lt _ _ hi,
    nsmul_zero]

private lemma restrictGT_triplet_of_gt (k i : Fin (3 * n)) (a : ℕ) (hi : k < i) :
    restrictGT k (a • triplet i) = a • triplet i := by
  rw [restrictGT_nsmul, triplet, restrictGT_nsmul,
    restrictGT_single_of_gt _ _ hi]

private lemma restrictGT_triplet_of_not_gt (k i : Fin (3 * n)) (a : ℕ)
    (hi : ¬k < i) : restrictGT k (a • triplet i) = 0 := by
  simp only [restrictGT_nsmul, triplet, restrictGT_single_of_not_gt _ _ hi,
    nsmul_zero]

private lemma restrictLT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictLT k (sequence j) = sequence j := by
  rw [sequence, restrictLT_add, restrictLT_add]
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
  rw [sequence, restrictLT_add, restrictLT_add]
  have h₀ : ¬(⟨j, by omega⟩ : Fin (3 * n)) < k := by
    change ¬j.val < k.val
    omega
  have h₁ : ¬(⟨j + 1, by omega⟩ : Fin (3 * n)) < k := by
    change ¬j.val + 1 < k.val
    omega
  have h₂ : ¬(⟨j + 2, by omega⟩ : Fin (3 * n)) < k := by
    change ¬j.val + 2 < k.val
    omega
  simp only [restrictLT_single_of_not_lt _ _ h₀,
    restrictLT_single_of_not_lt _ _ h₁,
    restrictLT_single_of_not_lt _ _ h₂, add_zero]

private lemma restrictGT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictGT k (sequence j) = sequence j := by
  rw [sequence, restrictGT_add, restrictGT_add]
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
  rw [sequence, restrictGT_add, restrictGT_add]
  have h₀ : ¬k < (⟨j, by omega⟩ : Fin (3 * n)) := by
    change ¬k.val < j.val
    omega
  have h₁ : ¬k < (⟨j + 1, by omega⟩ : Fin (3 * n)) := by
    change ¬k.val < j.val + 1
    omega
  have h₂ : ¬k < (⟨j + 2, by omega⟩ : Fin (3 * n)) := by
    change ¬k.val < j.val + 2
    omega
  simp only [restrictGT_single_of_not_gt _ _ h₀,
    restrictGT_single_of_not_gt _ _ h₁,
    restrictGT_single_of_not_gt _ _ h₂, add_zero]

private lemma meldable_zero : Meldable (0 : Hand n) := by
  use 0, 0
  simp

private lemma meldable_nsmul {c : Hand n} (hc : Meldable c) (a : ℕ) :
    Meldable (a • c) := by
  induction a with
  | zero => simpa using (meldable_zero : Meldable (0 : Hand n))
  | succ a ih => simpa only [succ_nsmul] using Meldable.add ih hc

private lemma meldable_sum {ι : Type*} {s : Finset ι} {f : ι → Hand n}
    (hf : ∀ i ∈ s, Meldable (f i)) : Meldable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (meldable_zero : Meldable (0 : Hand n))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        Meldable.add (hf i (Finset.mem_insert_self i s))
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
      simpa only [evalHom_apply, ← h] using hk
    simp only [map_add, map_sum, map_nsmul, evalHom_apply] at htotal
    have hseqsum : ∑ x, r x • (show Hand n from Mahjong.Hand.sequence x) k = 0 :=
      Nat.eq_zero_of_add_eq_zero_left htotal
    have hj : r j • (show Hand n from Mahjong.Hand.sequence j) k = 0 :=
      (Finset.sum_eq_zero_iff.mp hseqsum) j (Finset.mem_univ j)
    simpa only [hseq, smul_eq_mul, mul_one] using hj
  have hleft_eq :
      restrictLT k c =
          ∑ i, restrictLT k (t i • Mahjong.Hand.triplet i) +
          ∑ j, restrictLT k (r j • Mahjong.Hand.sequence j) := by
    simpa only [restrictLTHom_apply, map_add, map_sum] using
      congrArg (restrictLTHom k) h
  have hright_eq :
      restrictGT k c =
          ∑ i, restrictGT k (t i • Mahjong.Hand.triplet i) +
          ∑ j, restrictGT k (r j • Mahjong.Hand.sequence j) := by
    simpa only [restrictGTHom_apply, map_add, map_sum] using
      congrArg (restrictGTHom k) h
  constructor
  · rw [hleft_eq]
    apply Meldable.add
    · apply meldable_sum
      intro i _
      by_cases hi : i < k
      · simpa only [restrictLT_triplet_of_lt _ _ _ hi] using
          meldable_nsmul Meldable.triplet (t i)
      · simpa only [restrictLT_triplet_of_not_lt _ _ _ hi] using
          (meldable_zero : Meldable (0 : Hand n))
    · apply meldable_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simpa only [restrictLT_nsmul, restrictLT_sequence_of_left _ _ hj] using
          meldable_nsmul Meldable.sequence (r j)
      · by_cases hj' : k.val < j.val
        · simpa only [restrictLT_nsmul, restrictLT_sequence_of_right _ _ hj',
            nsmul_zero] using (meldable_zero : Meldable (0 : Hand n))
        · simpa only [hcross j hj hj', zero_nsmul, restrictLT_zero] using
            (meldable_zero : Meldable (0 : Hand n))
  · rw [hright_eq]
    apply Meldable.add
    · apply meldable_sum
      intro i _
      by_cases hi : k < i
      · simpa only [restrictGT_triplet_of_gt _ _ _ hi] using
          meldable_nsmul Meldable.triplet (t i)
      · simpa only [restrictGT_triplet_of_not_gt _ _ _ hi] using
          (meldable_zero : Meldable (0 : Hand n))
    · apply meldable_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simpa only [restrictGT_nsmul, restrictGT_sequence_of_left _ _ hj,
          nsmul_zero] using (meldable_zero : Meldable (0 : Hand n))
      · by_cases hj' : k.val < j.val
        · simpa only [restrictGT_nsmul, restrictGT_sequence_of_right _ _ hj'] using
            meldable_nsmul Meldable.sequence (r j)
        · simpa only [hcross j hj hj', zero_nsmul, restrictGT_zero] using
            (meldable_zero : Meldable (0 : Hand n))

private lemma restrictLT_pair_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (pair i) = pair i := by
  rw [pair, restrictLT_nsmul, restrictLT_single_of_lt _ _ hi]

private lemma restrictLT_pair_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (pair i) = 0 := by
  simp only [pair, restrictLT_nsmul, restrictLT_single_of_not_lt _ _ hi,
    nsmul_zero]

private lemma restrictGT_pair_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (pair i) = pair i := by
  rw [pair, restrictGT_nsmul, restrictGT_single_of_gt _ _ hi]

private lemma restrictGT_pair_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (pair i) = 0 := by
  simp only [pair, restrictGT_nsmul, restrictGT_single_of_not_gt _ _ hi,
    nsmul_zero]

private lemma restrictLT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n))
    (hi : i < k) :
    restrictLT k (c + single i) = restrictLT k c + single i := by
  rw [restrictLT_add, restrictLT_single_of_lt _ _ hi]

private lemma restrictGT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n))
    (hi : i < k) :
    restrictGT k (c + single i) = restrictGT k c := by
  simp only [restrictGT_add,
    restrictGT_single_of_not_gt _ _ (not_lt_of_ge (le_of_lt hi)), add_zero]

private lemma restrictLT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n))
    (hi : k < i) :
    restrictLT k (c + single i) = restrictLT k c := by
  simp only [restrictLT_add,
    restrictLT_single_of_not_lt _ _ (not_lt_of_ge (le_of_lt hi)), add_zero]

private lemma restrictGT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n))
    (hi : k < i) :
    restrictGT k (c + single i) = restrictGT k c + single i := by
  rw [restrictGT_add, restrictGT_single_of_gt _ _ hi]

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k = 0) :
    (size (restrictLT k w) % 3 = 2 ∧
      size (restrictGT k w) % 3 = 0 ∧ Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧
      size (restrictGT k w) % 3 = 2 ∧ Meldable (restrictLT k w)) := by
  obtain ⟨_, d, p, hd, hwd⟩ := hw
  have hzero : d k + pair p k = 0 := by
    simpa only [hwd, add_apply] using hk
  have hdk : d k = 0 := Nat.eq_zero_of_add_eq_zero_right hzero
  have hpair : pair p k = 0 := Nat.eq_zero_of_add_eq_zero_left hzero
  have hpk : p ≠ k := by
    rintro rfl
    simp [pair] at hpair
  obtain ⟨hdLT, hdGT⟩ := hd.split_at_zero k hdk
  rcases lt_or_gt_of_ne hpk with hleft | hright
  · left
    have hLT : restrictLT k w = restrictLT k d + pair p := by
      rw [hwd, restrictLT_add, restrictLT_pair_of_lt _ _ hleft]
    have hGT : restrictGT k w = restrictGT k d := by
      simp only [hwd, restrictGT_add,
        restrictGT_pair_of_not_gt _ _ (not_lt_of_ge (le_of_lt hleft)), add_zero]
    rw [hLT, hGT]
    refine ⟨?_, hdGT.size_mod_three, hdGT⟩
    simp [size_add, Nat.add_mod, hdLT.size_mod_three]
  · right
    have hLT : restrictLT k w = restrictLT k d := by
      simp only [hwd, restrictLT_add,
        restrictLT_pair_of_not_lt _ _ (not_lt_of_ge (le_of_lt hright)), add_zero]
    have hGT : restrictGT k w = restrictGT k d + pair p := by
      rw [hwd, restrictGT_add, restrictGT_pair_of_gt _ _ hright]
    rw [hLT, hGT]
    refine ⟨hdLT.size_mod_three, ?_, hdLT⟩
    simp [size_add, Nat.add_mod, hdGT.size_mod_three]

theorem interior_positive (hn : 2 ≤ n) (c : Hand n) (hc : IsFullWait c) :
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
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides
    · have hsize := hsides.1
      rw [restrictLT_add_single_of_lt c k i hi, size_add, size_single] at hsize
      omega
    · exact hsides.2.2
  have hright_meldable (i : Fin (3 * n)) (hi : k < i) :
      Meldable (restrictGT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_gt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides
    · exact hsides.2.2
    · have hsize := hsides.2.1
      rw [restrictGT_add_single_of_gt c k i hi, size_add, size_single] at hsize
      omega
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀ < k := by
      change 0 < k.val
      omega
    have hi₁ : i₁ < k := by
      change 1 < k.val
      omega
    have hsum₀ : (sum (restrictLT k c) + 0) % 3 = 0 := by
      simpa only [restrictLT_add_single_of_lt c k i₀ hi₀, sum_add, sum_single,
        i₀] using (hleft_meldable i₀ hi₀).sum_mod_three
    have hsum₁ : (sum (restrictLT k c) + 1) % 3 = 0 := by
      simpa only [restrictLT_add_single_of_lt c k i₁ hi₁, sum_add, sum_single,
        i₁] using (hleft_meldable i₁ hi₁).sum_mod_three
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
    have hsum₂ : (sum (restrictGT k c) + 2) % 3 = 0 := by
      simpa only [restrictGT_add_single_of_gt c k i₂ hi₂, sum_add, sum_single,
        i₂] using (hright_meldable i₂ hi₂).sum_mod_three
    have hsum₃ : (sum (restrictGT k c) + 3) % 3 = 0 := by
      simpa only [restrictGT_add_single_of_gt c k i₃ hi₃, sum_add, sum_single,
        i₃] using (hright_meldable i₃ hi₃).sum_mod_three
    omega

end Mahjong.Hand
