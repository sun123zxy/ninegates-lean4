/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Scan

/-! Canonical scans of equal prefixes agree, even for different orders. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma canonicalSequence_eq_of_coefficient_prefix {n N : ℕ} (c : VirtualHand n)
    (d : VirtualHand N) (k : ℕ)
    (same : ∀ j < k, coefficient c (j : ℤ) = coefficient d (j : ℤ)) :
    canonicalSequence c k = canonicalSequence d k := by
  exact congrArg (fun state : ℤ × ℤ ↦ state.1 % 3) (SequenceScan.run_congr k same)

lemma canonicalTriplet_eq_of_coefficient_prefix {n N : ℕ} (c : VirtualHand n)
    (d : VirtualHand N) (i : Rank n) (j : Rank N) (index : i.val = j.val)
    (same : ∀ k ≤ i.val, coefficient c (k : ℤ) = coefficient d (k : ℤ)) :
    canonicalTriplet c i = canonicalTriplet d j := by
  have tile : c i = d j := by
    rw [← coefficient_fin c i, ← coefficient_fin d j, ← index]
    exact same _ le_rfl
  rw [canonicalTriplet_eq, canonicalTriplet_eq, tile, index]
  rw [canonicalSequence_eq_of_coefficient_prefix c d j.val (fun k before ↦ same k (by omega)),
    canonicalSequence_eq_of_coefficient_prefix c d (j.val - 1) (fun k before ↦ same k (by omega))]

end Mahjong.VirtualHand
