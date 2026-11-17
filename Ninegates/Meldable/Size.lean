/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Size
public import Ninegates.Meldable.Basic

/-! Actual meldable hands have a nonnegative integral meld count. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

lemma Meldable.exists_size_eq (meldable : Meldable c) :
    ∃ k : ℕ, size c = 3 * (k : ℤ) := by
  have positive := meldable.nonnegative.size_nonnegative
  have residue := (ZMod.intCast_eq_intCast_iff' (size c) 0 3).mp
    meldable.virtuallyMeldable.size_cast
  norm_num only [Nat.cast_ofNat, Int.zero_emod] at residue
  refine ⟨(size c / 3).toNat, ?_⟩
  omega

lemma Meldable.size_ge_three (meldable : Meldable c) (nonzero : c ≠ 0) : 3 ≤ size c := by
  have positive := meldable.nonnegative.size_pos nonzero
  obtain ⟨k, count⟩ := meldable.exists_size_eq
  omega

end Mahjong.VirtualHand
