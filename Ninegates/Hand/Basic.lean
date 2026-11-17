/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Defs

/-! Elementary patterns and linear tile statistics for virtual hands. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma rankClass_eq_iff (i j : Rank n) : rankClass i = rankClass j ↔ i.val % 3 = j.val % 3 := by
  simp only [rankClass, rank, Int.cast_add, Int.cast_natCast, Int.cast_one,
    add_left_inj, ZMod.natCast_eq_natCast_iff']

lemma rankClass_rev_eq {i j : Rank n} (h : rankClass i = rankClass j) :
    rankClass i.rev = rankClass j.rev := by
  rw [rankClass_eq_iff] at h ⊢
  simp only [Fin.val_rev]
  have := i.isLt
  have := j.isLt
  omega

@[simp, grind =]
lemma nonnegative_iff (c : VirtualHand n) : Nonnegative c ↔ ∀ i, 0 ≤ c i := Iff.rfl

@[simp, grind =]
lemma bounded_iff (cap : ℕ) (c : VirtualHand n) :
    Bounded cap c ↔ (∀ i, 0 ≤ c i) ∧ ∀ i, c i ≤ cap := Iff.rfl

@[simp, grind =]
lemma valid_iff (c : VirtualHand n) : Valid c ↔ Bounded 4 c := Iff.rfl

@[grind =]
lemma single_apply (i j : Rank n) : single i j = if j = i then 1 else 0 := rfl

@[simp]
lemma single_self (i : Rank n) : single i i = 1 := by simp [single]

@[simp]
lemma single_of_ne {i j : Rank n} (h : j ≠ i) : single i j = 0 := by simp [single, h]

@[simp, grind =]
lemma pair_apply (i j : Rank n) : pair i j = 2 * single i j := rfl

@[simp, grind =]
lemma triplet_apply (i j : Rank n) : triplet i j = 3 * single i j := rfl

@[simp, grind =]
lemma reverse_apply (c : VirtualHand n) (i : Rank n) : reverse c i = c i.rev := rfl

@[simp, grind =]
lemma reverse_reverse (c : VirtualHand n) : reverse (reverse c) = c := by ext; simp

@[simp]
lemma nonnegative_single (i : Rank n) : Nonnegative (single i) := by
  intro j
  simp only [single]
  split <;> norm_num

@[simp]
lemma nonnegative_zero : Nonnegative (0 : VirtualHand n) := le_refl _

lemma Nonnegative.add {c d : VirtualHand n} (hc : Nonnegative c) (hd : Nonnegative d) :
    Nonnegative (c + d) := add_nonneg hc hd

lemma Nonnegative.size_nonnegative {c : VirtualHand n} (h : Nonnegative c) : 0 ≤ size c := by
  change 0 ≤ ∑ i, c i
  exact Finset.sum_nonneg fun i _ ↦ h i

@[simp]
lemma size_single (i : Rank n) : size (single i) = 1 := by simp [size, single]

@[simp]
lemma size_pair (i : Rank n) : size (pair i) = 2 := by rw [pair, map_smul]; simp

@[simp]
lemma size_triplet (i : Rank n) : size (triplet i) = 3 := by rw [triplet, map_smul]; simp

@[simp]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by simp [sequence]

@[simp]
lemma rankSum_single (i : Rank n) : rankSum (single i) = rank i := by
  simp [rankSum, single]

@[simp]
lemma rankSum_pair (i : Rank n) : rankSum (pair i) = 2 * rank i := by rw [pair, map_smul]; simp

@[simp]
lemma rankSum_triplet (i : Rank n) : rankSum (triplet i) = 3 * rank i := by
  rw [triplet, map_smul]; simp

@[simp]
lemma rankSum_sequence (i : Fin (3 * n - 2)) : rankSum (sequence i) = 3 * (i.val + 2) := by
  simp [sequence, rank]
  ring

@[grind =]
lemma classSize_single (r : ZMod 3) (i : Rank n) :
    classSize r (single i) = if rankClass i = r then 1 else 0 := by
  simp [classSize, single]

@[simp]
lemma classSize_pair (r : ZMod 3) (i : Rank n) :
    classSize r (pair i) = 2 * classSize r (single i) := by rw [pair, map_smul]; rfl

@[simp]
lemma classSize_triplet (r : ZMod 3) (i : Rank n) :
    classSize r (triplet i) = 3 * classSize r (single i) := by rw [triplet, map_smul]; rfl

/-- Proposition `prp-class-size-sum-congruence`, the class-size partition. -/
lemma size_eq_sum_classSize (c : VirtualHand n) : size c = ∑ r : ZMod 3, classSize r c := by
  simp only [classSize, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [size]

/-- The rank sum modulo three is determined by the three class sizes. -/
lemma rankSum_cast (c : VirtualHand n) :
    (rankSum c : ZMod 3) = ∑ r : ZMod 3, r * (classSize r c : ZMod 3) := by
  calc
    _ = ∑ i, rankClass i * (c i : ZMod 3) := by simp [rankSum, rankClass]
    _ = ∑ i : Rank n, ∑ r : ZMod 3,
        if rankClass i = r then r * (c i : ZMod 3) else 0 := by simp
    _ = ∑ r : ZMod 3, ∑ i : Rank n,
        if rankClass i = r then r * (c i : ZMod 3) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      simp [classSize, Finset.sum_filter, Finset.mul_sum, mul_ite]

private lemma sum_classes {A : Type*} [AddCommMonoid A] (f : ZMod 3 → A) :
    ∑ r, f r = f 0 + f 1 + f 2 := by
  have classes : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide +kernel
  have h01 : (0 : ZMod 3) ≠ 1 := by decide +kernel
  have h02 : (0 : ZMod 3) ≠ 2 := by decide +kernel
  have h12 : (1 : ZMod 3) ≠ 2 := by decide +kernel
  simp [classes, h01, h02, h12, add_assoc]

lemma size_eq_classSizes (c : VirtualHand n) :
    size c = classSize 0 c + classSize 1 c + classSize 2 c := by
  rw [size_eq_sum_classSize, sum_classes]

lemma rankSum_cast_eq_classSizes (c : VirtualHand n) :
    (rankSum c : ZMod 3) = (classSize 1 c : ZMod 3) + 2 * (classSize 2 c : ZMod 3) := by
  rw [rankSum_cast, sum_classes]
  simp

/-- The final equivalence in `prp-class-size-sum-congruence`. -/
lemma classSizes_congruent_iff (c : VirtualHand n) :
    ((classSize 0 c : ZMod 3) = (classSize 1 c : ZMod 3) ∧
      (classSize 1 c : ZMod 3) = (classSize 2 c : ZMod 3)) ↔
      (size c : ZMod 3) = 0 ∧ (rankSum c : ZMod 3) = 0 := by
  have three : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  have zero_mul (a : ZMod 3) : 3 * a = 0 := by rw [three, zero_mul]
  rw [size_eq_classSizes, rankSum_cast_eq_classSizes]
  push_cast
  constructor
  · rintro ⟨h01, h12⟩
    rw [h01, h12]
    constructor <;> linear_combination zero_mul (classSize 2 c)
  · rintro ⟨total, weighted⟩
    have h02 : (classSize 0 c : ZMod 3) = (classSize 2 c : ZMod 3) := by
      linear_combination total - weighted
    have h12 : (classSize 1 c : ZMod 3) = (classSize 2 c : ZMod 3) := by
      linear_combination weighted - zero_mul (classSize 2 c)
    exact ⟨h02.trans h12.symm, h12⟩

end Mahjong.VirtualHand
