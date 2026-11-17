/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Bounds

/-! The order-one full wait `(2,3,2)` attains both interchanging-class lower
bounds. Its class sizes also explain why the later `m=n+1` class-size theorem
must assume order at least two. -/

@[expose] public section

namespace Mahjong.Examples

open VirtualHand

def orderOneMiddleTriple : VirtualHand 1 := ![2, 3, 2]

private def orderOneMiddleTriplePairs : Rank 1 → Rank 1 := ![2, 1, 0]

private lemma orderOneMiddleTriple_drawPair (i : Rank 1) :
    DrawPair orderOneMiddleTriple i (orderOneMiddleTriplePairs i) := by
  fin_cases i <;> rw [DrawPair, meldable_iff_tripletGreedy] <;> decide +kernel

lemma orderOneMiddleTriple_isFullWait : IsFullWait 2 orderOneMiddleTriple := by
  rw [isFullWait_iff]
  refine ⟨?_, ?_, fun i ↦ ⟨orderOneMiddleTriplePairs i, orderOneMiddleTriple_drawPair i⟩⟩
  · intro i
    fin_cases i <;> norm_num [orderOneMiddleTriple]
  · norm_num [size, orderOneMiddleTriple, Fin.sum_univ_succ]

lemma orderOneMiddleTriple_fixedClass : fixedClass orderOneMiddleTriple = 2 := by decide +kernel

lemma orderOneMiddleTriple_classSizes : classSize 0 orderOneMiddleTriple = 2 ∧
    classSize 1 orderOneMiddleTriple = 2 ∧ classSize 2 orderOneMiddleTriple = 3 := by
  decide +kernel

end Mahjong.Examples
