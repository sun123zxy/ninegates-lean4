import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ}

def restrictLT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  AddMonoidHom.pi fun i => if i < k then count i else 0

def restrictGT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  AddMonoidHom.pi fun i => if k < i then count i else 0

@[simp]
lemma restrictLT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictLT k c i = if i < k then c i else 0 := by
  change (AddMonoidHom.pi fun i => if i < k then count i else 0) c i = _
  rw [AddMonoidHom.pi_apply]
  split <;> simp_all

@[simp]
lemma restrictGT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictGT k c i = if k < i then c i else 0 := by
  change (AddMonoidHom.pi fun i => if k < i then count i else 0) c i = _
  rw [AddMonoidHom.pi_apply]
  split <;> simp_all

@[simp]
lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

@[simp]
lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

@[simp]
lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

@[simp]
lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (single i) = 0 := by
  ext x
  by_cases hxi : x = i
  · subst x
    simp [hi]
  · simp [hxi]

@[simp]
lemma restrictLT_pair_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (pair i) = pair i := by
  simp [pair, hi]

@[simp]
lemma restrictLT_pair_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (pair i) = 0 := by
  simp [pair, hi]

@[simp]
lemma restrictGT_pair_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (pair i) = pair i := by
  simp [pair, hi]

@[simp]
lemma restrictGT_pair_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (pair i) = 0 := by
  simp [pair, hi]

@[simp]
lemma restrictGT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n)) (hi : i < k) :
    restrictGT k (c + single i) = restrictGT k c := by
  have hnot : ¬k < i := not_lt_of_ge (le_of_lt hi)
  simp [hnot]

@[simp]
lemma restrictLT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n)) (hi : k < i) :
    restrictLT k (c + single i) = restrictLT k c := by
  have hnot : ¬i < k := not_lt_of_ge (le_of_lt hi)
  simp [hnot]

private lemma restrictLT_triplet_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (triplet i) = triplet i := by
  rw [triplet, map_nsmul, restrictLT_single_of_lt _ _ hi]

private lemma restrictLT_triplet_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (triplet i) = 0 := by
  simp only [triplet, map_nsmul, restrictLT_single_of_not_lt _ _ hi, nsmul_zero]

private lemma restrictGT_triplet_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (triplet i) = triplet i := by
  rw [triplet, map_nsmul, restrictGT_single_of_gt _ _ hi]

private lemma restrictGT_triplet_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (triplet i) = 0 := by
  simp only [triplet, map_nsmul, restrictGT_single_of_not_gt _ _ hi, nsmul_zero]

private lemma restrictLT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictLT k (sequence j) = sequence j := by
  rw [sequence, map_add, map_add]
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
  rw [sequence, map_add, map_add]
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
  rw [sequence, map_add, map_add]
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
  rw [sequence, map_add, map_add]
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

theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : Fin (3 * n)) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  obtain ⟨⟨t, r⟩, h⟩ := hc
  have hc_eq :
      c = ∑ i, t i • Mahjong.Hand.triplet i +
        ∑ x, r x • Mahjong.Hand.sequence x := h.symm
  have htotal :
      count k
        (∑ i, t i • Mahjong.Hand.triplet i +
          ∑ x, r x • Mahjong.Hand.sequence x) = 0 := by
    simpa only [count_apply, ← hc_eq] using hk
  simp only [map_add, map_sum, map_nsmul] at htotal
  have hseqsum : ∑ x, r x • count k (Mahjong.Hand.sequence x) = 0 :=
    Nat.eq_zero_of_add_eq_zero_left htotal
  have hcross (j : Fin (3 * n - 2)) (hnotLeft : ¬j.val + 2 < k.val)
      (hnotRight : ¬k.val < j.val) : r j = 0 := by
    have hseq : count k (Mahjong.Hand.sequence j) = 1 := by
      change count k
        (single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
          single ⟨j + 2, by omega⟩) = 1
      simp only [map_add, count_apply, single_apply]
      split_ifs with h₀ h₁ h₂ <;> simp_all only [Fin.ext_iff]
      all_goals omega
    have hj : r j • count k (Mahjong.Hand.sequence j) = 0 :=
      (Finset.sum_eq_zero_iff.mp hseqsum) j (Finset.mem_univ j)
    simpa only [hseq, smul_eq_mul, mul_one] using hj
  constructor
  · rw [hc_eq, map_add, map_sum, map_sum]
    apply Meldable.add
    · apply Meldable.finset_sum
      intro i _
      by_cases hi : i < k
      · simpa only [map_nsmul, restrictLT_triplet_of_lt _ _ hi] using
          Meldable.triplet.nsmul (t i)
      · simpa only [map_nsmul, restrictLT_triplet_of_not_lt _ _ hi,
          nsmul_zero] using
          (Meldable.zero : Meldable (0 : Hand n))
    · apply Meldable.finset_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simpa only [map_nsmul, restrictLT_sequence_of_left _ _ hj] using
          Meldable.sequence.nsmul (r j)
      · by_cases hj' : k.val < j.val
        · simpa only [map_nsmul, restrictLT_sequence_of_right _ _ hj',
            nsmul_zero] using (Meldable.zero : Meldable (0 : Hand n))
        · simpa only [hcross j hj hj', zero_nsmul, map_zero] using
            (Meldable.zero : Meldable (0 : Hand n))
  · rw [hc_eq, map_add, map_sum, map_sum]
    apply Meldable.add
    · apply Meldable.finset_sum
      intro i _
      by_cases hi : k < i
      · simpa only [map_nsmul, restrictGT_triplet_of_gt _ _ hi] using
          Meldable.triplet.nsmul (t i)
      · simpa only [map_nsmul, restrictGT_triplet_of_not_gt _ _ hi,
          nsmul_zero] using
          (Meldable.zero : Meldable (0 : Hand n))
    · apply Meldable.finset_sum
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simpa only [map_nsmul, restrictGT_sequence_of_left _ _ hj,
          nsmul_zero] using (Meldable.zero : Meldable (0 : Hand n))
      · by_cases hj' : k.val < j.val
        · simpa only [map_nsmul, restrictGT_sequence_of_right _ _ hj'] using
            Meldable.sequence.nsmul (r j)
        · simpa only [hcross j hj hj', zero_nsmul, map_zero] using
            (Meldable.zero : Meldable (0 : Hand n))

end Mahjong.Hand
