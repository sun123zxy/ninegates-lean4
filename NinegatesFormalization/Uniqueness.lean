import NinegatesFormalization.Positivity
import NinegatesFormalization.Standard

namespace Mahjong.Hand

theorem full_wait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsFullWait) : c = standardFullWait n := by
  sorry

end Mahjong.Hand
