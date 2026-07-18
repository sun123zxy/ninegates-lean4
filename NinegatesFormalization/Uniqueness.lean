import Mathlib
import NinegatesFormalization.Basic
import NinegatesFormalization.Wait
import NinegatesFormalization.StandardFullWait

namespace Mahjong

namespace Hand

theorem full_wait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsFullWait) : c = standardFullWait n := by
  sorry

end Hand

end Mahjong
