/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Triplets

/-! Every sequence contributes one tile to each class. Differences between
class sizes must therefore be supplied by triplets in every meld placement. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma size_sequenceHand (s : Fin (3 * n - 2) → ℤ) :
    size (sequenceHand s) = 3 * ∑ j, s j := by
  simp only [sequenceHand, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    size_sequence, smul_eq_mul]
  simp [Finset.mul_sum, mul_comm]

@[simp]
lemma classSize_sequence (r : ZMod 3) (j : Fin (3 * n - 2)) : classSize r (sequence j) = 1 := by
  have virtual : VirtuallySequential (sequence j) := ⟨Pi.single j 1, by simp⟩
  have equal := (virtuallySequential_iff_classSizes _).mp virtual
  have total := size_eq_classSizes (sequence j)
  rw [size_sequence] at total
  have values : classSize 0 (sequence j) = 1 ∧ classSize 1 (sequence j) = 1 ∧
      classSize 2 (sequence j) = 1 := by omega
  have classes : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide +kernel
  rcases classes r with rfl | rfl | rfl <;> simp_all

namespace Placement

def sequenceCount (p : Placement n) : ℤ := ∑ j, p.seqNum j

lemma classSize_toHand (p : Placement n) (r : ZMod 3) :
    classSize r p.toHand = p.sequenceCount + 3 * classSize r p.tripNum := by
  rw [toHand_eq]
  simp only [map_add, map_smul, sequenceHand, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, classSize_sequence, sequenceCount, smul_eq_mul, mul_one]

lemma Nonnegative.sequenceCount_nonnegative {p : Placement n} (h : p.Nonnegative) :
    0 ≤ p.sequenceCount := Finset.sum_nonneg fun j _ ↦ h.1 j

lemma Nonnegative.sequenceCount_le_classSize {p : Placement n} (h : p.Nonnegative)
    (r : ZMod 3) : p.sequenceCount ≤ classSize r p.toHand := by
  rw [classSize_toHand]
  have triplets := Nonnegative.classSize_nonnegative h.2 r
  omega

lemma Nonnegative.triplet_le_hand {p : Placement n} (h : p.Nonnegative) (i : Rank n) :
    3 * p.tripNum i ≤ p.toHand i := by
  rw [toHand_apply]
  have a := coefficient_nonnegative h.1 i.val
  have b := coefficient_nonnegative h.1 ((i.val : ℤ) - 1)
  have c := coefficient_nonnegative h.1 ((i.val : ℤ) - 2)
  omega

end Placement

/-- A larger class must supply a removable triplet. This applies to any
actual meldable hand, independently of its size or the order. -/
lemma Meldable.exists_triplet_of_classSize_lt {c : VirtualHand n} (h : Meldable c)
    (r s : ZMod 3) (gap : classSize s c < classSize r c) :
    ∃ q : Rank n, rankClass q = r ∧ 3 ≤ c q ∧ Meldable (c - triplet q) := by
  obtain ⟨p, ⟨positive, canonical, rfl⟩, _⟩ := h.unique_canonical
  have triplets : 0 < classSize r p.tripNum := by
    rw [p.classSize_toHand s, p.classSize_toHand r] at gap
    have nonnegative := Nonnegative.classSize_nonnegative positive.2 s
    omega
  change 0 < ∑ i ∈ Finset.univ.filter (fun i : Rank n ↦ rankClass i = r), p.tripNum i at triplets
  obtain ⟨q, member, count⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ positive.2 i)).mp triplets
  refine ⟨q, (Finset.mem_filter.mp member).2, ?_, ?_⟩
  · have bound := positive.triplet_le_hand q
    omega
  · apply (h.sub_triplet_iff q).mpr
    rw [canonical.canonicalTriplet_eq]
    omega

end Mahjong.VirtualHand
