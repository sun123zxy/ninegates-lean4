import Mathlib
import NinegatesFormalization.Basic

namespace Mahjong.Hand

def standardFullWait (n : ℕ) : Hand n :=
  Hand.ofFn fun i ↦ if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1

theorem IsFullWait.standardFullWait (hn : 0 < n) : IsFullWait (standardFullWait n) := by
  sorry

end Mahjong.Hand
