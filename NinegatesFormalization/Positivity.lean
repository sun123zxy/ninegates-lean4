import Mathlib
import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ} (hn : 2 ≤ n)

theorem interior_positive (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i := by
  sorry

end Mahjong.Hand
