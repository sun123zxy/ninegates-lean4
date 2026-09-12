/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Winning.Defs

/-!
# Wait predicates

* `IsWaitingTile c i` tests whether adding tile `i` has a winning decomposition.
* `IsLiveWaitingTile c i` additionally requires the resulting hand to be valid.
* `IsWait` and `IsFullWait` allow dead tiles, while their `IsLive...` counterparts do not.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

def IsWaitingTile (c : Hand n) (i : Fin (3 * n)) : Prop := Winning (c + single i)

def IsLiveWaitingTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  IsWaitingTile c i ∧ Valid (c + single i)

def IsWait (c : Hand n) : Prop := ∃ i, IsWaitingTile c i

def IsLiveWait (c : Hand n) : Prop := ∃ i, IsLiveWaitingTile c i

def IsFullWait (c : Hand n) : Prop := ∀ i, IsWaitingTile c i

def IsLiveFullWait (c : Hand n) : Prop := ∀ i, IsLiveWaitingTile c i

end Mahjong.Hand
