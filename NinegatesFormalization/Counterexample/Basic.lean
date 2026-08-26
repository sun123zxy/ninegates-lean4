import NinegatesFormalization.Basic
import NinegatesFormalization.Standard

namespace Mahjong.Hand.Counterexample

abbrev IsCE {n : ℕ} (c : Hand n) : Prop :=
  IsFullWait c ∧ c ≠ standardFullWait n

abbrev HasCE (n : ℕ) : Prop :=
  ∃ c : Hand n, IsCE c

end Mahjong.Hand.Counterexample
