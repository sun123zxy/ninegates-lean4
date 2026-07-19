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
  change restrictLTHom k (a • (3 • single i)) = a • (3 • single i)
  rw [map_nsmul, map_nsmul]
  simp only [restrictLTHom_apply]
  rw [restrictLT_single_of_lt _ _ hi]

private lemma restrictLT_triplet_of_not_lt (k i : Fin (3 * n)) (a : ℕ)
    (hi : ¬i < k) : restrictLT k (a • triplet i) = 0 := by
  change restrictLTHom k (a • (3 • single i)) = _
  rw [map_nsmul, map_nsmul]
  simp only [restrictLTHom_apply]
  rw [restrictLT_single_of_not_lt _ _ hi]
  simp

private lemma restrictGT_triplet_of_gt (k i : Fin (3 * n)) (a : ℕ) (hi : k < i) :
    restrictGT k (a • triplet i) = a • triplet i := by
  change restrictGTHom k (a • (3 • single i)) = a • (3 • single i)
  rw [map_nsmul, map_nsmul]
  simp only [restrictGTHom_apply]
  rw [restrictGT_single_of_gt _ _ hi]

private lemma restrictGT_triplet_of_not_gt (k i : Fin (3 * n)) (a : ℕ)
    (hi : ¬k < i) : restrictGT k (a • triplet i) = 0 := by
  change restrictGTHom k (a • (3 • single i)) = _
  rw [map_nsmul, map_nsmul]
  simp only [restrictGTHom_apply]
  rw [restrictGT_single_of_not_gt _ _ hi]
  simp

private lemma restrictLT_sequence_of_left (k : Fin (3 * n))
    (j : Fin (3 * n - 2)) (hj : j.val + 2 < k.val) :
    restrictLT k (sequence j) = sequence j := by
  change restrictLTHom k
      (single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
        single ⟨j + 2, by omega⟩) =
      single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
        single ⟨j + 2, by omega⟩
  rw [map_add, map_add]
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
  change restrictLTHom k
      (single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
        single ⟨j + 2, by omega⟩) = _
  rw [map_add, map_add]
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
  change restrictGTHom k
      (single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
        single ⟨j + 2, by omega⟩) =
      single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
        single ⟨j + 2, by omega⟩
  rw [map_add, map_add]
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
  change restrictGTHom k
      (single ⟨j, by omega⟩ + single ⟨j + 1, by omega⟩ +
        single ⟨j + 2, by omega⟩) = _
  rw [map_add, map_add]
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
    rw [h]
    change restrictLTHom k
        (∑ i, t i • Mahjong.Hand.triplet i +
          ∑ j, r j • Mahjong.Hand.sequence j) = _
    simp only [map_add, map_sum, restrictLTHom_apply]
  have hright_eq :
      restrictGT k c =
        ∑ i, restrictGT k (t i • Mahjong.Hand.triplet i) +
          ∑ j, restrictGT k (r j • Mahjong.Hand.sequence j) := by
    rw [h]
    change restrictGTHom k
        (∑ i, t i • Mahjong.Hand.triplet i +
          ∑ j, r j • Mahjong.Hand.sequence j) = _
    simp only [map_add, map_sum, restrictGTHom_apply]
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
      · change Meldable
          (restrictLTHom k (r j • Mahjong.Hand.sequence j))
        rw [map_nsmul]
        simp only [restrictLTHom_apply]
        rw [restrictLT_sequence_of_left _ _ hj]
        exact meldable_nsmul Meldable.sequence _
      · by_cases hj' : k.val < j.val
        · change Meldable
            (restrictLTHom k (r j • Mahjong.Hand.sequence j))
          rw [map_nsmul]
          simp only [restrictLTHom_apply]
          rw [restrictLT_sequence_of_right _ _ hj']
          exact meldable_zero
        · rw [hcross j hj hj']
          simp only [zero_nsmul]
          change Meldable (restrictLTHom k 0)
          rw [map_zero]
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
      · change Meldable
          (restrictGTHom k (r j • Mahjong.Hand.sequence j))
        rw [map_nsmul]
        simp only [restrictGTHom_apply]
        rw [restrictGT_sequence_of_left _ _ hj]
        exact meldable_zero
      · by_cases hj' : k.val < j.val
        · change Meldable
            (restrictGTHom k (r j • Mahjong.Hand.sequence j))
          rw [map_nsmul]
          simp only [restrictGTHom_apply]
          rw [restrictGT_sequence_of_right _ _ hj']
          exact meldable_nsmul Meldable.sequence _
        · rw [hcross j hj hj']
          simp only [zero_nsmul]
          change Meldable (restrictGTHom k 0)
          rw [map_zero]
          exact meldable_zero

end Mahjong.Hand
