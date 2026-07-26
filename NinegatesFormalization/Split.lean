import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ}

def filter (keep : Fin (3 * n) → Prop) [DecidablePred keep] : Hand n →+ Hand n where
  toFun c := ⟨fun i ↦ if keep i then c i else 0⟩
  map_zero' := by ext i; grind
  map_add' _ _ := by ext i; grind

@[simp, grind =]
lemma filter_single (keep : Fin (3 * n) → Prop) [DecidablePred keep]
    (i : Fin (3 * n)) :
    filter keep (single i) = if keep i then single i else 0 := by
  ext j
  by_cases hi : keep i <;> by_cases hji : j = i <;>
    simp [filter, single, hi, hji]

def restrictLT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  filter (· < k)

def restrictGT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  filter (k < ·)

namespace Meldable.Placement

def filter
    (tripKeep : Fin (3 * n) → Prop) [DecidablePred tripKeep]
    (seqKeep : Fin (3 * n - 2) → Prop) [DecidablePred seqKeep] :
    Placement n →+ Placement n where
  toFun p :=
    ⟨fun i ↦ if tripKeep i then p.tripNum i else 0,
      fun j ↦ if seqKeep j then p.seqNum j else 0⟩
  map_zero' := by ext i <;> grind
  map_add' _ _ := by ext i <;> grind

def restrictLT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (· < k) (fun j ↦ j.val + 2 < k.val)

def restrictGT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (k < ·) (fun j ↦ k.val < j.val)

end Meldable.Placement

@[simp, grind =]
lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by
  simp [restrictLT, hi]

@[simp, grind =]
lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by
  simp [restrictLT, hi]

@[simp, grind =]
lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by
  simp [restrictGT, hi]

@[simp, grind =]
lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (single i) = 0 := by
  simp [restrictGT, hi]

@[simp, grind =]
lemma restrictLT_pair_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (pair i) = pair i := by
  simp [pair, hi]

@[simp, grind =]
lemma restrictLT_pair_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (pair i) = 0 := by
  simp [pair, hi]

@[simp, grind =]
lemma restrictGT_pair_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (pair i) = pair i := by
  simp [pair, hi]

@[simp, grind =]
lemma restrictGT_pair_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (pair i) = 0 := by
  simp [pair, hi]

@[local grind =]
private lemma restrictLT_triplet_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (triplet i) = triplet i := by
  simp [triplet, hi]

@[local grind =]
private lemma restrictLT_triplet_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (triplet i) = 0 := by
  simp [triplet, hi]

@[local grind =]
private lemma restrictGT_triplet_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (triplet i) = triplet i := by
  simp [triplet, hi]

@[local grind =]
private lemma restrictGT_triplet_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (triplet i) = 0 := by
  simp [triplet, hi]

@[local grind =]
private lemma restrictLT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictLT k (sequence j) = sequence j := by
  grind

@[local grind =]
private lemma restrictLT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictLT k (sequence j) = 0 := by
  grind

@[local grind =]
private lemma restrictGT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictGT k (sequence j) = sequence j := by
  grind

@[local grind =]
private lemma restrictGT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictGT k (sequence j) = 0 := by
  grind

@[grind →]
theorem Meldable.IsWitness.split_at_zero {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : Fin (3 * n)) (hk : c k = 0) :
    IsWitness (Meldable.Placement.restrictLT k p) (restrictLT k c) ∧
      IsWitness (Meldable.Placement.restrictGT k p) (restrictGT k c) := by
  have hp_eq : p.toHand = c := hp
  have hseqsum : ∑ x, p.seqNum x • Mahjong.Hand.sequence x k = 0 :=
    by grind
  have hcross (j : Fin (3 * n - 2)) (hnotLeft : ¬j.val + 2 < k.val)
      (hnotRight : ¬k.val < j.val) : p.seqNum j = 0 := by
    have hseq : Mahjong.Hand.sequence j k = 1 := by
      grind [Mahjong.Hand.sequence, Mahjong.Hand.single]
    have hj : p.seqNum j • Mahjong.Hand.sequence j k = 0 :=
      (Finset.sum_eq_zero_iff.mp hseqsum) j (Finset.mem_univ j)
    simpa only [hseq, smul_eq_mul, mul_one] using hj
  have hLT :
      (Meldable.Placement.restrictLT k p).toHand = restrictLT k c := by
    rw [Meldable.Placement.toHand_eq_sum, ← hp_eq,
      Meldable.Placement.toHand_eq_sum]
    simp only [Meldable.Placement.restrictLT, Meldable.Placement.filter]
    rw [map_add, map_sum, map_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i < k
      · simp [hi, restrictLT_triplet_of_lt _ _ hi]
      · simp [hi, restrictLT_triplet_of_not_lt _ _ hi]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simp [hj, restrictLT_sequence_of_left _ _ hj]
      · by_cases hj' : k.val < j.val
        · simp [hj, restrictLT_sequence_of_right _ _ hj']
        · simp [hj, hcross j hj hj']
  have hGT :
      (Meldable.Placement.restrictGT k p).toHand = restrictGT k c := by
    rw [Meldable.Placement.toHand_eq_sum, ← hp_eq,
      Meldable.Placement.toHand_eq_sum]
    simp only [Meldable.Placement.restrictGT, Meldable.Placement.filter]
    rw [map_add, map_sum, map_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : k < i
      · simp [hi, restrictGT_triplet_of_gt _ _ hi]
      · simp [hi, restrictGT_triplet_of_not_gt _ _ hi]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val + 2 < k.val
      · have hj' : ¬k.val < j.val := by omega
        simp [hj', restrictGT_sequence_of_left _ _ hj]
      · by_cases hj' : k.val < j.val
        · simp [hj', restrictGT_sequence_of_right _ _ hj']
        · simp [hj', hcross j hj hj']
  exact ⟨hLT, hGT⟩

@[grind →]
theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : Fin (3 * n)) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  grind [Meldable]

end Mahjong.Hand
