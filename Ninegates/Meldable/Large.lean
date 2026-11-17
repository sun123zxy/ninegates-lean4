/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Triplets

/-! Seven tiles at one rank force a triplet in the canonical placement. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

lemma Meldable.sub_triplet_of_seven (meldable : Meldable c) (i : Rank n) (large : 7 ≤ c i) :
    Meldable (c - triplet i) := by
  apply (meldable.sub_triplet_iff i).mpr
  have previous := canonicalSequence_bounds c i.val
  have older := canonicalSequence_bounds c (i.val - 1)
  rw [canonicalTriplet_eq]
  omega

end Mahjong.VirtualHand
