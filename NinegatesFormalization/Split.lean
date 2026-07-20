import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ}

def filter (keep : Fin (3 * n) → Prop) [DecidablePred keep] : Hand n →+ Hand n :=
  AddMonoidHom.pi fun i => if keep i then count i else 0

@[simp]
lemma filter_apply (keep : Fin (3 * n) → Prop) [DecidablePred keep]
    (c : Hand n) (i : Fin (3 * n)) :
    filter keep c i = if keep i then c i else 0 := by
  change (AddMonoidHom.pi fun i => if keep i then count i else 0) c i = _
  rw [AddMonoidHom.pi_apply]
  split <;> simp_all

@[simp]
lemma filter_single (keep : Fin (3 * n) → Prop) [DecidablePred keep]
    (i : Fin (3 * n)) :
    filter keep (single i) = if keep i then single i else 0 := by
  ext j
  by_cases hi : keep i <;> by_cases hji : j = i <;> simp_all

def restrictLT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  filter (· < k)

def restrictGT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  filter (k < ·)

@[simp]
lemma restrictLT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictLT k c i = if i < k then c i else 0 := by
  exact filter_apply (· < k) c i

@[simp]
lemma restrictGT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictGT k c i = if k < i then c i else 0 := by
  exact filter_apply (k < ·) c i

namespace Meldable.Placement

def filter
    (tripKeep : Fin (3 * n) → Prop) [DecidablePred tripKeep]
    (seqKeep : Fin (3 * n - 2) → Prop) [DecidablePred seqKeep] :
    Placement n →+ Placement n where
  toFun p :=
    ⟨fun i ↦ if tripKeep i then p.tripNum i else 0,
      fun j ↦ if seqKeep j then p.seqNum j else 0⟩
  map_zero' := by
    ext i
    · change (if tripKeep i then 0 else 0) = 0
      split <;> rfl
    · change (if seqKeep i then 0 else 0) = 0
      split <;> rfl
  map_add' p q := by
    ext i
    · change (if tripKeep i then p.tripNum i + q.tripNum i else 0) =
        (if tripKeep i then p.tripNum i else 0) +
          (if tripKeep i then q.tripNum i else 0)
      split <;> rfl
    · change (if seqKeep i then p.seqNum i + q.seqNum i else 0) =
        (if seqKeep i then p.seqNum i else 0) +
          (if seqKeep i then q.seqNum i else 0)
      split <;> rfl

@[simp]
lemma filter_tripNum
    (tripKeep : Fin (3 * n) → Prop) [DecidablePred tripKeep]
    (seqKeep : Fin (3 * n - 2) → Prop) [DecidablePred seqKeep]
    (p : Placement n) (i : Fin (3 * n)) :
    (filter tripKeep seqKeep p).tripNum i =
      if tripKeep i then p.tripNum i else 0 := rfl

@[simp]
lemma filter_seqNum
    (tripKeep : Fin (3 * n) → Prop) [DecidablePred tripKeep]
    (seqKeep : Fin (3 * n - 2) → Prop) [DecidablePred seqKeep]
    (p : Placement n) (j : Fin (3 * n - 2)) :
    (filter tripKeep seqKeep p).seqNum j =
      if seqKeep j then p.seqNum j else 0 := rfl

def restrictLT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (· < k) (fun j ↦ j.val + 2 < k.val)

def restrictGT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (k < ·) (fun j ↦ k.val < j.val)

@[simp]
lemma restrictLT_tripNum (k : Fin (3 * n)) (p : Placement n) (i : Fin (3 * n)) :
    (restrictLT k p).tripNum i = if i < k then p.tripNum i else 0 := rfl

@[simp]
lemma restrictLT_seqNum (k : Fin (3 * n)) (p : Placement n)
    (j : Fin (3 * n - 2)) :
    (restrictLT k p).seqNum j = if j.val + 2 < k.val then p.seqNum j else 0 := rfl

@[simp]
lemma restrictGT_tripNum (k : Fin (3 * n)) (p : Placement n) (i : Fin (3 * n)) :
    (restrictGT k p).tripNum i = if k < i then p.tripNum i else 0 := rfl

@[simp]
lemma restrictGT_seqNum (k : Fin (3 * n)) (p : Placement n)
    (j : Fin (3 * n - 2)) :
    (restrictGT k p).seqNum j = if k.val < j.val then p.seqNum j else 0 := rfl

end Meldable.Placement

@[simp]
lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by
  simp [restrictLT, hi]

@[simp]
lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by
  simp [restrictLT, hi]

@[simp]
lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by
  simp [restrictGT, hi]

@[simp]
lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (single i) = 0 := by
  simp [restrictGT, hi]

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
  simp [restrictGT, not_lt_of_ge (le_of_lt hi)]

@[simp]
lemma restrictLT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n)) (hi : k < i) :
    restrictLT k (c + single i) = restrictLT k c := by
  simp [restrictLT, not_lt_of_ge (le_of_lt hi)]

private lemma restrictLT_triplet_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (triplet i) = triplet i := by
  simp [triplet, hi]

private lemma restrictLT_triplet_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (triplet i) = 0 := by
  simp [triplet, hi]

private lemma restrictGT_triplet_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (triplet i) = triplet i := by
  simp [triplet, hi]

private lemma restrictGT_triplet_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (triplet i) = 0 := by
  simp [triplet, hi]

private lemma restrictLT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictLT k (sequence j) = sequence j := by
  rw [sequence, map_add, map_add]
  have h₀ : (⟨j, by omega⟩ : Fin (3 * n)) < k := by
    apply Fin.mk_lt_mk.mpr
    omega
  have h₁ : (⟨j + 1, by omega⟩ : Fin (3 * n)) < k := by
    apply Fin.mk_lt_mk.mpr
    omega
  have h₂ : (⟨j + 2, by omega⟩ : Fin (3 * n)) < k := by
    apply Fin.mk_lt_mk.mpr
    omega
  rw [restrictLT_single_of_lt _ _ h₀, restrictLT_single_of_lt _ _ h₁,
    restrictLT_single_of_lt _ _ h₂]

private lemma restrictLT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictLT k (sequence j) = 0 := by
  rw [sequence, map_add, map_add]
  have h₀ : ¬(⟨j, by omega⟩ : Fin (3 * n)) < k := by
    intro h
    have h' := Fin.mk_lt_mk.mp h
    omega
  have h₁ : ¬(⟨j + 1, by omega⟩ : Fin (3 * n)) < k := by
    intro h
    have h' := Fin.mk_lt_mk.mp h
    omega
  have h₂ : ¬(⟨j + 2, by omega⟩ : Fin (3 * n)) < k := by
    intro h
    have h' := Fin.mk_lt_mk.mp h
    omega
  simp only [restrictLT_single_of_not_lt _ _ h₀,
    restrictLT_single_of_not_lt _ _ h₁,
    restrictLT_single_of_not_lt _ _ h₂, add_zero]

private lemma restrictGT_sequence_of_right (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : k.val < j.val) :
    restrictGT k (sequence j) = sequence j := by
  rw [sequence, map_add, map_add]
  have h₀ : k < (⟨j, by omega⟩ : Fin (3 * n)) := by
    apply Fin.mk_lt_mk.mpr
    omega
  have h₁ : k < (⟨j + 1, by omega⟩ : Fin (3 * n)) := by
    apply Fin.mk_lt_mk.mpr
    omega
  have h₂ : k < (⟨j + 2, by omega⟩ : Fin (3 * n)) := by
    apply Fin.mk_lt_mk.mpr
    omega
  rw [restrictGT_single_of_gt _ _ h₀, restrictGT_single_of_gt _ _ h₁,
    restrictGT_single_of_gt _ _ h₂]

private lemma restrictGT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictGT k (sequence j) = 0 := by
  rw [sequence, map_add, map_add]
  have h₀ : ¬k < (⟨j, by omega⟩ : Fin (3 * n)) := by
    intro h
    have h' := Fin.mk_lt_mk.mp h
    omega
  have h₁ : ¬k < (⟨j + 1, by omega⟩ : Fin (3 * n)) := by
    intro h
    have h' := Fin.mk_lt_mk.mp h
    omega
  have h₂ : ¬k < (⟨j + 2, by omega⟩ : Fin (3 * n)) := by
    intro h
    have h' := Fin.mk_lt_mk.mp h
    omega
  simp only [restrictGT_single_of_not_gt _ _ h₀,
    restrictGT_single_of_not_gt _ _ h₁,
    restrictGT_single_of_not_gt _ _ h₂, add_zero]

theorem Meldable.IsWitness.split_at_zero {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : Fin (3 * n)) (hk : c k = 0) :
    IsWitness (Meldable.Placement.restrictLT k p) (restrictLT k c) ∧
      IsWitness (Meldable.Placement.restrictGT k p) (restrictGT k c) := by
  have hp_eq : p.toHand = c := hp
  have htotal : count k p.toHand = 0 := by
    rw [hp_eq, count_apply]
    exact hk
  rw [Meldable.Placement.count_toHand] at htotal
  have hseqsum : ∑ x, p.seqNum x • count k (Mahjong.Hand.sequence x) = 0 :=
    Nat.eq_zero_of_add_eq_zero_left htotal
  have hcross (j : Fin (3 * n - 2)) (hnotLeft : ¬j.val + 2 < k.val)
      (hnotRight : ¬k.val < j.val) : p.seqNum j = 0 := by
    have hseq : count k (Mahjong.Hand.sequence j) = 1 := by
      change count k
        (single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
          single ⟨j + 2, by omega⟩) = 1
      simp only [map_add, count_apply, single_apply]
      split_ifs with h₀ h₁ h₂ <;> simp_all only [Fin.ext_iff]
      all_goals omega
    have hj : p.seqNum j • count k (Mahjong.Hand.sequence j) = 0 :=
      (Finset.sum_eq_zero_iff.mp hseqsum) j (Finset.mem_univ j)
    simpa only [hseq, smul_eq_mul, mul_one] using hj
  have hLT :
      (Meldable.Placement.restrictLT k p).toHand = restrictLT k c := by
    rw [Meldable.Placement.toHand_eq_sum, ← hp_eq,
      Meldable.Placement.toHand_eq_sum]
    simp only [Meldable.Placement.restrictLT_tripNum,
      Meldable.Placement.restrictLT_seqNum]
    rw [map_add, map_sum, map_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i < k
      · simp only [if_pos hi, map_nsmul, restrictLT_triplet_of_lt _ _ hi]
      · simp only [if_neg hi, zero_nsmul, map_nsmul,
          restrictLT_triplet_of_not_lt _ _ hi, nsmul_zero]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val + 2 < k.val
      · simp only [if_pos hj, map_nsmul, restrictLT_sequence_of_left _ _ hj]
      · by_cases hj' : k.val < j.val
        · simp only [if_neg hj, zero_nsmul, map_nsmul,
            restrictLT_sequence_of_right _ _ hj', nsmul_zero]
        · simp only [if_neg hj, hcross j hj hj', zero_nsmul, map_zero]
  have hGT :
      (Meldable.Placement.restrictGT k p).toHand = restrictGT k c := by
    rw [Meldable.Placement.toHand_eq_sum, ← hp_eq,
      Meldable.Placement.toHand_eq_sum]
    simp only [Meldable.Placement.restrictGT_tripNum,
      Meldable.Placement.restrictGT_seqNum]
    rw [map_add, map_sum, map_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : k < i
      · simp only [if_pos hi, map_nsmul, restrictGT_triplet_of_gt _ _ hi]
      · simp only [if_neg hi, zero_nsmul, map_nsmul,
          restrictGT_triplet_of_not_gt _ _ hi, nsmul_zero]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val + 2 < k.val
      · have hj' : ¬k.val < j.val := by omega
        simp only [if_neg hj', zero_nsmul, map_nsmul,
          restrictGT_sequence_of_left _ _ hj, nsmul_zero]
      · by_cases hj' : k.val < j.val
        · simp only [if_pos hj', map_nsmul, restrictGT_sequence_of_right _ _ hj']
        · simp only [if_neg hj', hcross j hj hj', zero_nsmul, map_zero]
  exact ⟨hLT, hGT⟩

theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : Fin (3 * n)) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨hLT, hGT⟩ := hp.split_at_zero k hk
  exact ⟨⟨_, hLT⟩, ⟨_, hGT⟩⟩

end Mahjong.Hand
