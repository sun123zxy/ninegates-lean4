import Ninegates.Basic
import Ninegates.Standard
import Ninegates.Wait.Basic

namespace Mahjong.Hand.Counterexample

abbrev IsCE {n : ℕ} (c : Hand n) : Prop :=
  IsFullWait c ∧ c ≠ standardFullWait n

abbrev HasCE (n : ℕ) : Prop :=
  ∃ c : Hand n, IsCE c

end Mahjong.Hand.Counterexample
