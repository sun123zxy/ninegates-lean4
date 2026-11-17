/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Periodic

/-! The sequence recurrence's response to one added tile. -/

@[expose] public section

namespace Mahjong.VirtualHand.SequenceImpulse

def value (p k : ℤ) : ℤ := if p ≤ k then Periodic.value 1 (-1) 0 (k - p) else 0

lemma convolution (p k : ℤ) :
    value p k + value p (k - 1) + value p (k - 2) = if k = p then 1 else 0 := by
  unfold value Periodic.value
  split_ifs <;> omega

end Mahjong.VirtualHand.SequenceImpulse
