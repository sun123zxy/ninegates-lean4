import Mathlib
import NinegatesFormalization.Basic


namespace Mahjong

namespace Hand

variable {n : ℕ}

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + single i)

lemma IsWait.Valid (c : Hand n) (hc : IsWait c) : Valid c := by
  rcases hc with ⟨i, hi⟩
  intro j
  exact le_trans (Nat.le_add_right (c j) (single i j)) (hi.1 j)

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + single i)

end Hand

end Mahjong
