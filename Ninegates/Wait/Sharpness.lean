/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Segment
public import Ninegates.Meldable.Statistics
public import Ninegates.Meldable.Triplets
public import Ninegates.Wait.Graph
public import Ninegates.Wait.Reverse

/-! The general sharpness witness in the remark after Proposition 5.6 of
arXiv:2611.06944v1: `(0,3,3,3,1^(3n-5),3)` for every `n >= 2`. The three
asserted families of draw-pair edges have explicit interval decompositions. -/

@[expose] public section

namespace Mahjong.VirtualHand.ClassBoundSharpness

variable {n : ℕ}

def hand (n : ℕ) : VirtualHand n :=
  interiorOnes + (2 : ℤ) • segment 1 4 + (3 : ℤ) • singleAt (3 * n - 1)

@[grind =]
lemma hand_apply (order : 2 ≤ n) (i : Rank n) :
    hand n i = if i.val = 0 then 0 else
      if i.val ≤ 3 ∨ i.val + 1 = 3 * n then 3 else 1 := by
  have bound := i.isLt
  simp only [hand, Pi.add_apply, Pi.smul_apply, smul_eq_mul, interiorOnes_apply,
    segment_apply, singleAt_apply]
  split_ifs <;> omega

lemma hand_eq (order : 2 ≤ n) (r : Fin (3 * n - 2)) (start : r.val = 1)
    (last : Rank n) (finish : last.val + 1 = 3 * n) :
    hand n = interiorOnes + (2 : ℤ) • sequence r + triplet last := by
  rw [sequence_eq_segment]
  ext i
  simp only [hand, Pi.add_apply, Pi.smul_apply, smul_eq_mul, segment_apply,
    singleAt_apply, triplet_apply, single_apply, Fin.ext_iff, start]
  split_ifs <;> omega

lemma size_hand (order : 2 ≤ n) : size (hand n) = 3 * (n : ℤ) + 7 := by
  let r : Fin (3 * n - 2) := ⟨1, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  rw [hand_eq order r rfl last (by dsimp [last]; omega), map_add, map_add, map_smul,
    size_sequence, size_triplet, interiorOnes_eq_segment, size_segment (by omega)]
  simp only [smul_eq_mul]
  push_cast
  omega

lemma drawPair_self (order : 2 ≤ n) (i : Rank n) (fixed : rankClass i = 2) :
    DrawPair (hand n) i i := by
  let r : Fin (3 * n - 2) := ⟨1, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  have residue := (rankClass_eq_two_iff i).mp fixed
  have bound := i.isLt
  have core : Sequential (interiorOnes - single i) := by
    rw [interiorOnes_eq_segment]
    exact sequential_segment_sub_single (by omega) i (by omega) (by omega)
      (by omega) (by omega)
  have double : Sequential ((2 : ℤ) • sequence r) := by
    rw [sequence_eq_segment]
    exact (sequential_segment (by omega) (by dsimp [r]; omega) (by omega)).smul (by norm_num)
  change Meldable (hand n + single i - pair i)
  have shape : hand n + single i - pair i =
      (interiorOnes - single i + (2 : ℤ) • sequence r) + triplet last := by
    rw [hand_eq order r rfl last (by dsimp [last]; omega), pair]
    module
  rw [shape]
  exact ((core.add double).meldable).add_triplet last

lemma drawPair_last (order : 2 ≤ n) (i last : Rank n)
    (class_i : rankClass i = 1) (finish : last.val + 1 = 3 * n) :
    DrawPair (hand n) i last := by
  let first : Rank n := ⟨0, by omega⟩
  let r : Fin (3 * n - 2) := ⟨1, by omega⟩
  have residue := (rankClass_eq_one_iff i).mp class_i
  have bound := i.isLt
  have core : Sequential (segment 0 (3 * n) - single first + single i) :=
    sequential_segment_sub_first_add_single le_rfl first i rfl (by omega)
      (by omega) (by omega) (by omega)
  have double : Sequential ((2 : ℤ) • sequence r) := by
    rw [sequence_eq_segment]
    exact (sequential_segment (by omega) (by dsimp [r]; omega) (by omega)).smul (by norm_num)
  have shape : hand n + single i - pair last =
      (segment 0 (3 * n) - single first + single i) + (2 : ℤ) • sequence r := by
    rw [hand_eq order r rfl last finish]
    ext j
    have bound_j := j.isLt
    simp only [Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply, single_apply,
      Fin.ext_iff, interiorOnes_apply, segment_apply]
    dsimp only [first]
    split_ifs <;> omega
  change Meldable _
  rw [shape]
  exact (core.add double).meldable

lemma drawPair_fourth (order : 2 ≤ n) (i fourth : Rank n)
    (class_i : rankClass i = 0) (at_fourth : fourth.val = 3) :
    DrawPair (hand n) i fourth := by
  let second : Rank n := ⟨1, by omega⟩
  let third : Rank n := ⟨2, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  have residue := (rankClass_eq_zero_iff i).mp class_i
  have bound := i.isLt
  have core : Sequential (segment 2 (3 * n - 1) - single third + single i) :=
    sequential_segment_sub_first_add_single (by omega) third i rfl (by omega)
      (by omega) (by omega) (by omega)
  have shape : hand n + single i - pair fourth =
      (segment 2 (3 * n - 1) - single third + single i) +
        triplet second + triplet third + triplet last := by
    ext j
    have bound_j := j.isLt
    simp only [hand_apply order, Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply,
      single_apply, Fin.ext_iff, segment_apply, at_fourth]
    dsimp only [second, third, last]
    split_ifs <;> omega
  change Meldable _
  rw [shape]
  exact ((core.meldable.add_triplet second).add_triplet third).add_triplet last

lemma full (order : 2 ≤ n) : IsFullWait (n + 2) (hand n) := by
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hand_apply order]
    split_ifs <;> norm_num
  · rw [size_hand order]
    push_cast
    ring
  · intro i
    rcases three_classes_exhaust 0 1 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (rankClass i) with class_i | class_i | class_i
    · exact ⟨⟨3, by omega⟩, drawPair_fourth order i _ class_i rfl⟩
    · exact ⟨⟨3 * n - 1, by omega⟩,
        drawPair_last order i _ class_i (by dsimp; omega)⟩
    · exact ⟨i, drawPair_self order i class_i⟩

lemma fixedClass_hand (order : 2 ≤ n) : fixedClass (hand n) = 2 := by
  let i : Rank n := ⟨1, by omega⟩
  exact (drawPair_self order i rfl).self_fixed_class.symm

lemma classSize_one (order : 2 ≤ n) : classSize 1 (hand n) = (n : ℤ) + 1 := by
  let r : Fin (3 * n - 2) := ⟨1, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  have class_last : rankClass last = 0 := by
    rw [rankClass_eq_zero_iff]
    dsimp [last]
    omega
  rw [hand_eq order r rfl last (by dsimp [last]; omega), map_add, map_add, map_smul,
    classSize_sequence, classSize_triplet, classSize_single, class_last,
    classSize_interiorOnes_nonTwo (by omega) 1 (by decide +kernel)]
  norm_num
  omega

/-- Reversal supplies a witness attaining the other interchanging-class bound. -/
lemma reverse_sharp (order : 2 ≤ n) :
    IsFullWait (n + 2) (reverse (hand n)) ∧ fixedClass (reverse (hand n)) = 2 ∧
      classSize 0 (reverse (hand n)) = (n : ℤ) + 1 := by
  refine ⟨(full order).reverse, ?_, ?_⟩
  · rw [(full order).fixedClass_reverse, fixedClass_hand order]
    decide +kernel
  · simpa only [classSize_reverse, sub_zero] using classSize_one order

end Mahjong.VirtualHand.ClassBoundSharpness
