/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Winning.Defs
public import Ninegates.Meldable.Basic

/-!
# Basic properties of winning hands
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

lemma Winning.size {c : Hand n} (hc : Winning c) : size c = 3 * n + 5 := hc.1

theorem Winning.reverse {c : Hand n} (hc : Winning c) : Winning (reverse c) := by
  obtain ⟨hs, d, i, hd, h⟩ := hc
  refine ⟨by simpa using hs, Hand.reverse d, i.rev, hd.reverse, ?_⟩
  simp [h]

end Mahjong.Hand
