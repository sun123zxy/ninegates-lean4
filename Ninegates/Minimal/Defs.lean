/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Defs

/-! Minimality is with respect to removing an arbitrary nonzero meldable hand,
and permits the remaining full wait to have any meld count. -/

@[expose] public section

namespace Mahjong.VirtualHand

structure IsMinimalFullWait {n : ℕ} (m : ℕ) (c : VirtualHand n) : Prop where
  full : IsFullWait m c
  minimal : ∀ {k : ℕ} {remainder removed : VirtualHand n},
    IsFullWait k remainder → Meldable removed → c = remainder + removed → removed = 0

end Mahjong.VirtualHand
