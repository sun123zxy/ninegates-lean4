import Ninegates.Counterexample.Reduction

/-!

# Uniqueness of the full wait

The main theorem of our project.
-/

namespace Mahjong.Hand

theorem liveFullWait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsLiveFullWait) : c = standardLiveFullWait n := by
  sorry

end Mahjong.Hand
