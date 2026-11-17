/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Examples
public import Ninegates.Wait.TwoPair
public import Ninegates.Wait.Classes

/-! The paper's two qualifications: two-pair decompositions need not be unique
at larger meld counts, and an incoming fixed-class vertex need not have a loop. -/

@[expose] public section

namespace Mahjong.Examples

open VirtualHand

lemma largeHand_twoPair_left : TwoPair largeHand (1 : Rank 2) 3 := by
  refine ⟨by decide, ⟨⟨![0, 0, 2, 0], ![0, 0, 0, 0, 0, 1]⟩, ?_, ?_⟩⟩
  · constructor <;> intro i <;> fin_cases i <;> norm_num
  · ext i
    fin_cases i <;> norm_num [Placement.toHand_apply, coefficient, largeHand, pair, single,
      Matrix.vecHead, Matrix.vecTail]

lemma largeHand_twoPair_right : TwoPair largeHand (3 : Rank 2) 4 := by
  refine ⟨by decide, ⟨⟨![0, 2, 0, 0], ![0, 0, 0, 0, 0, 1]⟩, ?_, ?_⟩⟩
  · constructor <;> intro i <;> fin_cases i <;> norm_num
  · ext i
    fin_cases i <;> norm_num [Placement.toHand_apply, coefficient, largeHand, pair, single,
      Matrix.vecHead, Matrix.vecTail]

def fixedNoLoop : VirtualHand 3 := ![2, 2, 2, 3, 3, 2, 4, 1, 3]

private def fixedNoLoopPairs : Rank 3 → Rank 3 := ![1, 0, 8, 4, 0, 5, 4, 6, 5]

private lemma fixedNoLoop_drawPair (i : Rank 3) : DrawPair fixedNoLoop i (fixedNoLoopPairs i) := by
  fin_cases i <;> rw [DrawPair, meldable_iff_tripletGreedy] <;> decide +kernel

lemma fixedNoLoop_isFullWait : IsFullWait 7 fixedNoLoop := by
  rw [isFullWait_iff]
  refine ⟨?_, ?_, fun i ↦ ⟨fixedNoLoopPairs i, fixedNoLoop_drawPair i⟩⟩
  · intro i
    fin_cases i <;> norm_num [fixedNoLoop]
  · norm_num [size, fixedNoLoop, Fin.sum_univ_succ]

lemma fixedNoLoop_fixedClass : fixedClass fixedNoLoop = 0 := by decide +kernel

lemma fixedNoLoop_incoming (i : Rank 3) :
    DrawPair fixedNoLoop i 8 ↔ i = 2 ∨ i = 5 := by
  fin_cases i <;> rw [DrawPair, meldable_iff_tripletGreedy] <;> decide +kernel

lemma fixedNoLoop_no_self : ¬DrawPair fixedNoLoop (8 : Rank 3) 8 := by
  rw [fixedNoLoop_incoming]
  decide +kernel

end Mahjong.Examples
