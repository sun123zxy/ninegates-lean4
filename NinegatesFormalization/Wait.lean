import Mathlib
import NinegatesFormalization.Model

namespace Mahjong

namespace Hand

variable {n : ℕ}

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + single i)

lemma IsWait.Valid (c : Hand n) (hc : IsWait c) : Valid c := by
  rcases hc with ⟨i, hi⟩
  intro j
  exact le_trans (Nat.le_add_right (c j) (single i j)) (hi.1 j)

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + single i)

def standardFullWait (n : ℕ) : Hand n :=
  fun i ↦ if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1

theorem IsFullWait.standardFullWait (hn : 0 < n) : IsFullWait (standardFullWait n) := by
  sorry

theorem full_wait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsFullWait) : c = standardFullWait n := by
  sorry

end Hand

end Mahjong
