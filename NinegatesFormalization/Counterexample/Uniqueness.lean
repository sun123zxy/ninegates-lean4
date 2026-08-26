import NinegatesFormalization.Counterexample.Reduction

/-!

# Uniqueness of the full wait

The main theorem of our project.
-/

namespace Mahjong.Hand

theorem full_wait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsFullWait) : c = standardFullWait n := by
  sorry

end Mahjong.Hand
