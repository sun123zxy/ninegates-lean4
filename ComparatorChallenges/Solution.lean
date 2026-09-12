import Ninegates.Counterexample.Reduction

namespace ComparatorChallenges

open Mahjong
open Hand
open Counterexample

theorem fullWait_reduction {n : ℕ} (hn : 2 ≤ n) {c : Hand n} (hc : IsCE c) :
    ∃ m, 2 ≤ m ∧ m ≤ 7 ∧ HasCE m :=
  Hand.fullWait_reduction hn hc

end ComparatorChallenges
