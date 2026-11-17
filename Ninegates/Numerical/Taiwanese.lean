/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Next
public import Mathlib.SetTheory.Cardinal.Finite

/-! The nonminimal Taiwanese waits are the distinct standard hands with one
additional elementary meld. The remaining numerical counts are separate. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma Standard.nextNonminimal_three_card : (nextNonminimal 3).card = 122 := by
  decide +kernel

lemma taiwanese_nonminimal_card :
    Nat.card {c : VirtualHand 3 // IsFullWait 5 c ∧ ¬IsMinimalFullWait 5 c} = 122 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun c ↦ next_nonminimal_iff_mem (by decide) c))]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Standard.nextNonminimal_three_card

end Mahjong.VirtualHand
