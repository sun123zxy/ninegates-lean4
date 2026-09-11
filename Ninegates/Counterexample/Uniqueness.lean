/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Counterexample.Elimination

/-!

# Uniqueness of the full wait

The main theorem of our project.
-/

@[expose] public section

namespace Mahjong.Hand

theorem liveFullWait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsLiveFullWait) : c = Standard.A n := by
  have hfull := (isLiveFullWait_iff_le_three.mp hc).1
  have hfamily := Counterexample.fullWait_classification n hn c hfull
  rcases hfamily with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact False.elim ((Standard.B.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.B'.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.C.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.C'.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.D.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.D'.not_isLiveFullWait n hn) hc)
  · exact False.elim ((Standard.E.not_isLiveFullWait n hn) hc)

end Mahjong.Hand
