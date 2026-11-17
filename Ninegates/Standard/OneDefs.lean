/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Defs

/-! The six explicitly named order-one hands. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

def One : Fin 6 → VirtualHand 1 :=
  ![![3, 1, 3], ![2, 3, 2], ![3, 3, 1], ![1, 3, 3], ![3, 2, 2], ![2, 2, 3]]

def OrderOneFamily (c : VirtualHand 1) : Prop := ∃ k, c = One k

end Mahjong.VirtualHand.Standard
