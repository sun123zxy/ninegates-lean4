/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Classes

/-! The hand with one copy at every interior rank and zero at both boundaries.
Subtracting this lower bound turns interior positivity into nonnegative excess. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def interiorOnes : VirtualHand n := fun i ↦ if 0 < i.val ∧ i.val + 1 < 3 * n then 1 else 0

@[grind =]
lemma interiorOnes_apply (i : Rank n) :
    interiorOnes i = if 0 < i.val ∧ i.val + 1 < 3 * n then 1 else 0 := rfl

lemma interiorOnes_bounds (i : Rank n) : 0 ≤ interiorOnes i ∧ interiorOnes i ≤ 1 := by
  unfold interiorOnes
  split_ifs <;> norm_num

lemma rankClass_eq_one_iff (i : Rank n) : rankClass i = 1 ↔ i.val % 3 = 0 := by
  simp only [rankClass, rank, Int.cast_add, Int.cast_natCast, Int.cast_one]
  change (i.val : ZMod 3) + 1 = (0 : ZMod 3) + 1 ↔ i.val % 3 = 0
  simp only [add_left_inj]
  exact ZMod.natCast_eq_natCast_iff' i.val 0 3

lemma rankClass_eq_zero_iff (i : Rank n) : rankClass i = 0 ↔ i.val % 3 = 2 := by
  simp only [rankClass, rank, Int.cast_add, Int.cast_natCast, Int.cast_one]
  change (i.val : ZMod 3) + 1 = (2 : ZMod 3) + 1 ↔ i.val % 3 = 2
  simp only [add_left_inj]
  exact ZMod.natCast_eq_natCast_iff' i.val 2 3

lemma rankClass_eq_two_iff (i : Rank n) : rankClass i = 2 ↔ i.val % 3 = 1 := by
  have two : (2 : ZMod 3) = 1 + 1 := by decide +kernel
  simp only [rankClass, rank, Int.cast_add, Int.cast_natCast, Int.cast_one, two,
    add_left_inj]
  exact ZMod.natCast_eq_natCast_iff' i.val 1 3

def excess (c : VirtualHand n) : VirtualHand n := c - interiorOnes

@[simp, grind =]
lemma excess_apply (c : VirtualHand n) (i : Rank n) : excess c i = c i - interiorOnes i := rfl

@[simp]
lemma classSize_excess (c : VirtualHand n) (r : ZMod 3) :
    classSize r (excess c) = classSize r c - classSize r (interiorOnes : VirtualHand n) := by
  exact map_sub (classSize r) c interiorOnes

lemma classSize_interiorOnes (positive : 0 < n) (r : ZMod 3) :
    classSize r (interiorOnes : VirtualHand n) =
      n - (if r = 1 then 1 else 0) - (if r = 0 then 1 else 0) := by
  let first : Rank n := ⟨0, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  have decomposition : interiorOnes = (fun _ : Rank n ↦ (1 : ℤ)) - single first - single last := by
    ext i
    have bound := i.isLt
    simp only [interiorOnes, Pi.sub_apply, single_apply, Fin.ext_iff]
    dsimp only [first, last]
    split_ifs <;> omega
  have first_class : rankClass first = 1 := rfl
  have last_class : rankClass last = 0 := by
    have value : rank last = (3 * n : ℕ) := by dsimp [rank, last]; omega
    rw [rankClass, value]
    push_cast
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  rw [decomposition]
  simp only [map_sub, classSize_const, classSize_single, first_class, last_class, mul_one]
  congr 2 <;> simp only [eq_comm]

lemma classSize_interiorOnes_ge (positive : 0 < n) (r : ZMod 3) :
    (n : ℤ) - 1 ≤ classSize r (interiorOnes : VirtualHand n) := by
  rw [classSize_interiorOnes positive]
  have different : (0 : ZMod 3) ≠ 1 := by decide +kernel
  split_ifs <;> simp_all

lemma classSize_interiorOnes_two (positive : 0 < n) :
    classSize 2 (interiorOnes : VirtualHand n) = n := by
  rw [classSize_interiorOnes positive]
  simp only [ite_eq_right (show (2 : ZMod 3) ≠ 1 by decide +kernel),
    ite_eq_right (show (2 : ZMod 3) ≠ 0 by decide +kernel), sub_zero]

lemma classSize_interiorOnes_nonTwo (positive : 0 < n) (r : ZMod 3) (boundary : r ≠ 2) :
    classSize r (interiorOnes : VirtualHand n) = (n : ℤ) - 1 := by
  rw [classSize_interiorOnes positive]
  have classes : r = 0 ∨ r = 1 ∨ r = 2 := by
    have all : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide +kernel
    exact all r
  rcases classes with rfl | rfl | rfl <;> simp_all

lemma exists_boundary_rank (positive : 0 < n) (r : ZMod 3) (boundary : r ≠ 2) :
    ∃ i : Rank n, rankClass i = r ∧ interiorOnes i = 0 := by
  have classes : r = 0 ∨ r = 1 := by
    have all : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide +kernel
    rcases all r with h | h | h <;> simp_all
  rcases classes with rfl | rfl
  · let last : Rank n := ⟨3 * n - 1, by omega⟩
    refine ⟨last, ?_, ?_⟩
    · have value : rank last = (3 * n : ℕ) := by dsimp [rank, last]; omega
      rw [rankClass, value]
      push_cast
      rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
    · simp only [interiorOnes, last]
      have at_end : ¬(3 * n - 1 + 1 < 3 * n) := by omega
      simp [at_end]
  · refine ⟨⟨0, by omega⟩, rfl, ?_⟩
    simp [interiorOnes]

end Mahjong.VirtualHand
