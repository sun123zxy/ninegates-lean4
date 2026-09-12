/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Meldable.Defs

/-!
# Winning hands

A `Winning c` hand has `3 * n + 5` tiles and can be written as a meldable hand plus
one pair. Physical tile availability is tracked separately by `Valid`.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

def Winning (c : Hand n) : Prop :=
  size c = 3 * n + 5 ∧
    ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + pair i

end Mahjong.Hand
