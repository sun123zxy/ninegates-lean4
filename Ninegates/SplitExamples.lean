/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Positive

/-! Nonnegativity is essential for splitting at a zero rank. Also, the
three-rank hand with a missing middle rank can wait on both sides without
waiting on the middle rank. -/

@[expose] public section

namespace Mahjong.Examples

open VirtualHand

def signedCut : VirtualHand 2 := single 0 - single 3

lemma signedCut_virtuallySequential : VirtuallySequential signedCut := by
  refine ⟨![1, -1, 0, 0], ?_⟩
  ext i
  fin_cases i <;> norm_num [sequenceHand_apply, coefficient, signedCut, single]

lemma signedCut_missing : signedCut (1 : Rank 2) = 0 := by decide +kernel

lemma signedCut_left_not_virtuallyMeldable : ¬VirtuallyMeldable (leftOf 1 signedCut) := by
  intro virtual
  have one : size (leftOf 1 signedCut) = 1 := by decide +kernel
  have zero := virtual.size_cast
  rw [one] at zero
  norm_num at zero

def outerWait : VirtualHand 1 := ![2, 0, 2]

lemma outerWait_left : DrawPair outerWait (0 : Rank 1) 2 := by
  rw [DrawPair, meldable_iff_tripletGreedy]
  decide +kernel

lemma outerWait_right : DrawPair outerWait (2 : Rank 1) 0 := by
  rw [DrawPair, meldable_iff_tripletGreedy]
  decide +kernel

lemma outerWait_middle (j : Rank 1) : ¬DrawPair outerWait (1 : Rank 1) j := by
  fin_cases j <;> rw [DrawPair, meldable_iff_tripletGreedy] <;> decide +kernel

lemma outerWait_not_full : ¬IsFullWait 1 outerWait := by
  intro full
  obtain ⟨j, edge⟩ := (isFullWait_iff.mp full).2.2 1
  exact outerWait_middle j edge

end Mahjong.Examples
