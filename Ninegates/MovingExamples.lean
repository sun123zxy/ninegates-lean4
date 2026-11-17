/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.SequentialMoving

/-! Examples separating the obstructions in the tile-moving criteria. -/

@[expose] public section

namespace Mahjong.Examples

open VirtualHand

/-- Borrow and carry cancel on the two middle ranks. No middle triplets are
available, so the third row of the table would fail, but the fourth succeeds. -/
def borrowCarry : Placement 2 := ⟨![0, 2, 0, 0], ![1, 0, 0, 0, 0, 0]⟩

lemma borrowCarry_canonical_step : (Moving.step borrowCarry 0).canonicalize =
    (⟨![2, 0, 0, 0], ![0, 0, 0, 1, 0, 0]⟩ : Placement 2) := by
  ext i <;> fin_cases i <;>
    norm_num [Moving.step, Moving.shift, Placement.canonicalize, borrowCarry,
      Moving.sequenceAt, Pi.single_apply, coefficient, Matrix.vecHead, Matrix.vecTail]

lemma borrowCarry_move_meldable : Meldable (Moving.right borrowCarry.toHand 0) := by
  rw [← Moving.toHand_step, ← Placement.toHand_canonicalize, borrowCarry_canonical_step]
  refine ⟨_, ?_, rfl⟩
  constructor <;> intro i <;> fin_cases i <;> norm_num

/-- Availability of a source tile and a source triplet is insufficient when
the neighbouring sequence cannot supply a carry. -/
def missingBorrow : Placement 2 := ⟨0, ![1, 0, 1, 0, 0, 0]⟩

lemma missingBorrow_meldable : Meldable missingBorrow.toHand := by
  refine ⟨missingBorrow, ?_, rfl⟩
  constructor <;> intro i <;> fin_cases i <;> norm_num [missingBorrow]

lemma missingBorrow_source_available : 1 ≤ missingBorrow.toHand (0 : Rank 2) := by
  norm_num [Placement.toHand_apply, coefficient, missingBorrow]

lemma missingBorrow_move_not_meldable : ¬Meldable (Moving.right missingBorrow.toHand 0) := by
  have canonical : missingBorrow.Canonic := by intro i; norm_num [missingBorrow]
  rw [Moving.meldable_right_iff canonical]
  · norm_num [missingBorrow, Moving.sequenceAt, Moving.rankAt]
  · constructor <;> intro i <;> fin_cases i <;> norm_num [missingBorrow]

/-- A first step can succeed even though a later required sequence is absent. -/
def shortSequence : Fin 7 → ℤ := ![1, 0, 0, 0, 0, 0, 0]

lemma shortSequence_first_step :
    Sequential (moveTile (sequenceHand shortSequence) (0 : Rank 3) 3) := by
  change Sequential (Moving.right (sequenceHand shortSequence) (0 : Moving.Start 3))
  apply (Moving.sequential_right_iff (n := 3) (s := shortSequence)
    (by intro r; fin_cases r <;> norm_num [shortSequence]) 0).mpr
  norm_num [shortSequence, Moving.sequenceAt]

lemma shortSequence_long_move_fails :
    ¬Sequential (moveTile (sequenceHand shortSequence) (0 : Rank 3) 6) := by
  intro result
  have required := ((sequential_moveTile_right_iff (n := 3) (s := shortSequence)
    (by intro r; fin_cases r <;> norm_num [shortSequence]) 0 6 (by decide)).mp result).2
  have missing := required 3 (by decide) (by decide) (by decide)
  norm_num [shortSequence] at missing

end Mahjong.Examples
