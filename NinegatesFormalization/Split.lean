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

lemma restrictLT_add (k : Fin (3 * n)) (c d : Hand n) :
    restrictLT k (c + d) = restrictLT k c + restrictLT k d := by
  rw [← restrictLTHom_apply, map_add, restrictLTHom_apply, restrictLTHom_apply]

lemma restrictGT_add (k : Fin (3 * n)) (c d : Hand n) :
    restrictGT k (c + d) = restrictGT k c + restrictGT k d := by
  rw [← restrictGTHom_apply, map_add, restrictGTHom_apply, restrictGTHom_apply]

lemma restrictLT_nsmul (k : Fin (3 * n)) (a : ℕ) (c : Hand n) :
    restrictLT k (a • c) = a • restrictLT k c := by
  rw [← restrictLTHom_apply, map_nsmul, restrictLTHom_apply]

lemma restrictGT_nsmul (k : Fin (3 * n)) (a : ℕ) (c : Hand n) :
    restrictGT k (a • c) = a • restrictGT k c := by
  rw [← restrictGTHom_apply, map_nsmul, restrictGTHom_apply]

private lemma restrictLT_zero (k : Fin (3 * n)) :
    restrictLT k (0 : Hand n) = 0 := by
  rw [← restrictLTHom_apply, map_zero]

private lemma restrictGT_zero (k : Fin (3 * n)) :
    restrictGT k (0 : Hand n) = 0 := by
  rw [← restrictGTHom_apply, map_zero]

lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
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
    · apply Meldable.finset_sum
      intro i _
      by_cases hi : i < k
      · simpa only [restrictLT_triplet_of_lt _ _ _ hi] using
          Meldable.triplet.nsmul (t i)
      · simpa only [restrictLT_triplet_of_not_lt _ _ _ hi] using
          (Meldable.zero : Meldable (0 : Hand n))
    · apply Meldable.finset_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simpa only [restrictLT_nsmul, restrictLT_sequence_of_left _ _ hj] using
          Meldable.sequence.nsmul (r j)
      · by_cases hj' : k.val < j.val
        · simpa only [restrictLT_nsmul, restrictLT_sequence_of_right _ _ hj',
            nsmul_zero] using (Meldable.zero : Meldable (0 : Hand n))
        · simpa only [hcross j hj hj', zero_nsmul, restrictLT_zero] using
            (Meldable.zero : Meldable (0 : Hand n))
  · rw [hright_eq]
    apply Meldable.add
    · apply Meldable.finset_sum
      intro i _
      by_cases hi : k < i
      · simpa only [restrictGT_triplet_of_gt _ _ _ hi] using
          Meldable.triplet.nsmul (t i)
      · simpa only [restrictGT_triplet_of_not_gt _ _ _ hi] using
          (Meldable.zero : Meldable (0 : Hand n))
    · apply Meldable.finset_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simpa only [restrictGT_nsmul, restrictGT_sequence_of_left _ _ hj,
          nsmul_zero] using (Meldable.zero : Meldable (0 : Hand n))
      · by_cases hj' : k.val < j.val
        · simpa only [restrictGT_nsmul, restrictGT_sequence_of_right _ _ hj'] using
            Meldable.sequence.nsmul (r j)
        · simpa only [hcross j hj hj', zero_nsmul, restrictGT_zero] using
            (Meldable.zero : Meldable (0 : Hand n))

end Mahjong.Hand
