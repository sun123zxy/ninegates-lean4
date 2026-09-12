import Ninegates.Wait.Defs
import Ninegates.Standard.Defs
import Ninegates.Counterexample.Defs

namespace ComparatorChallenges

open Mahjong
open Hand
open Counterexample

theorem fullWait_reduction {n : ℕ} (hn : 2 ≤ n) {c : Hand n} (hc : IsCE c) :
    ∃ m, 2 ≤ m ∧ m ≤ 7 ∧ HasCE m :=
  sorry

theorem isFullWait_iff_eightFamily (n : Nat) (hn : 2 ≤ n) (c : Hand n) :
    IsFullWait c ↔ IsEightFamily c :=
  sorry

theorem orderOne_isFullWait_iff_isOrderOneFamily (c : Hand 1) :
    IsFullWait c ↔ IsOrderOneFamily c :=
  sorry

theorem liveFullWait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsLiveFullWait) : c = Standard.A n :=
  sorry

end ComparatorChallenges
