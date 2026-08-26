import NinegatesFormalization.Basic
import NinegatesFormalization.Standard

namespace Mahjong.Hand

abbrev IsCounterexample {n : ℕ} (c : Hand n) : Prop :=
  IsFullWait c ∧ c ≠ standardFullWait n

abbrev HasCounterexample (n : ℕ) : Prop :=
  ∃ c : Hand n, IsCounterexample c

end Mahjong.Hand
