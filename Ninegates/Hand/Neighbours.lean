/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Classes

/-! Each of the other two congruence classes occurs among two consecutive
neighbours of a rank. The distances are the nonzero residues modulo three. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma exists_class_before (j : Rank n) (room : 2 ≤ j.val) (r : ZMod 3)
    (different : r ≠ rankClass j) :
    ∃ i : Rank n, i.val < j.val ∧ j.val ≤ i.val + 2 ∧ rankClass i = r := by
  let distance := (rankClass j - r).val
  have positive : 0 < distance := ZMod.val_pos.mpr (sub_ne_zero.mpr different.symm)
  have small : distance < 3 := ZMod.val_lt _
  let i : Rank n := ⟨j.val - distance, by have := j.isLt; omega⟩
  refine ⟨i, by dsimp [i]; omega, by dsimp [i]; omega, ?_⟩
  have value : rank i = rank j - distance := by dsimp [rank, i]; omega
  rw [rankClass, value, Int.cast_sub, Int.cast_natCast]
  change rankClass j - ((distance : ℕ) : ZMod 3) = r
  simp [distance]

lemma exists_class_after (j : Rank n) (room : j.val + 2 < 3 * n) (r : ZMod 3)
    (different : r ≠ rankClass j) :
    ∃ i : Rank n, j.val < i.val ∧ i.val ≤ j.val + 2 ∧ rankClass i = r := by
  let distance := (r - rankClass j).val
  have positive : 0 < distance := ZMod.val_pos.mpr (sub_ne_zero.mpr different)
  have small : distance < 3 := ZMod.val_lt _
  let i : Rank n := ⟨j.val + distance, by omega⟩
  refine ⟨i, by dsimp [i]; omega, by dsimp [i]; omega, ?_⟩
  have value : rank i = rank j + distance := by dsimp [rank, i]; omega
  rw [rankClass, value, Int.cast_add, Int.cast_natCast]
  change rankClass j + ((distance : ℕ) : ZMod 3) = r
  simp [distance]

end Mahjong.VirtualHand
