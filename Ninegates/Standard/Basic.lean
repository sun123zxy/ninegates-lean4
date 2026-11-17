/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Defs

/-! Coordinate patterns and reflection of the standard families. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

variable {n : ℕ}

@[grind =]
lemma A_apply (i : Rank n) : A n i = if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1 := by
  have bound := i.isLt
  simp only [A, Pi.add_apply, Pi.smul_apply, smul_eq_mul, interiorOnes_apply, singleAt_apply]
  split_ifs <;> omega

@[grind =]
lemma B_apply (order : 2 ≤ n) (i : Rank n) :
    B n i = if i.val = 0 then 3 else if i.val = 3 * n - 4 then 4
      else if i.val + 1 = 3 * n then 0 else 1 := by
  have bound := i.isLt
  simp only [B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, interiorOnes_apply, singleAt_apply]
  split_ifs <;> omega

@[grind =]
lemma C_apply (order : 2 ≤ n) (i : Rank n) :
    C n i = if i.val = 2 then 4 else if i.val = 3 * n - 2 then 3
      else if i.val + 1 = 3 * n then 0 else 1 := by
  have bound := i.isLt
  simp only [C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, segment_apply, singleAt_apply]
  split_ifs <;> omega

@[grind =]
lemma D_apply (order : 2 ≤ n) (i : Rank n) :
    D n i = if i.val = 0 ∨ i.val + 1 = 3 * n then 0 else if i.val = 2 then 4
      else if i.val = 3 then 2 else if i.val = 3 * n - 2 then 3 else 1 := by
  have bound := i.isLt
  simp only [D, Pi.add_apply, Pi.smul_apply, smul_eq_mul, segment_apply, singleAt_apply]
  split_ifs <;> omega

@[grind =]
lemma E_apply (order : 2 ≤ n) (i : Rank n) :
    E n i = if i.val = 0 ∨ i.val + 1 = 3 * n then 0
      else if i.val = 3 ∨ i.val = 3 * n - 4 then 4 else 1 := by
  have bound := i.isLt
  simp only [E, Pi.add_apply, Pi.smul_apply, smul_eq_mul, interiorOnes_apply, singleAt_apply]
  split_ifs <;> omega

@[simp]
lemma reverse_A (n : ℕ) : reverse (A n) = A n := by
  ext i
  have bound := i.isLt
  simp only [reverse_apply, A_apply, Fin.val_rev]
  split_ifs <;> omega

@[simp]
lemma reverse_E (order : 2 ≤ n) : reverse (E n) = E n := by
  ext i
  have bound := i.isLt
  simp only [reverse_apply, E_apply order, Fin.val_rev]
  split_ifs <;> omega

lemma B'_eq (order : 2 ≤ n) :
    B' n = interiorOnes + (3 : ℤ) • singleAt 3 + (3 : ℤ) • singleAt (3 * n - 1) := by
  ext i
  have bound := i.isLt
  simp only [B', reverse_apply, B_apply order, Fin.val_rev, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, interiorOnes_apply, singleAt_apply]
  split_ifs <;> omega

lemma EightFamily.reverse (order : 2 ≤ n) {c : VirtualHand n} (h : EightFamily c) :
    EightFamily (reverse c) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [EightFamily, B', C', D', reverse_reverse, reverse_A, reverse_E order]
    tauto

end Mahjong.VirtualHand.Standard
