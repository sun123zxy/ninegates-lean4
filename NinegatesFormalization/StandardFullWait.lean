import Mathlib
import NinegatesFormalization.Basic
import NinegatesFormalization.Wait

namespace Mahjong

namespace Hand

def standardFullWait (n : ℕ) : Hand n :=
  fun i ↦ if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1

theorem IsFullWait.standardFullWait (hn : 0 < n) : IsFullWait (standardFullWait n) := by
  sorry

end Hand

end Mahjong
