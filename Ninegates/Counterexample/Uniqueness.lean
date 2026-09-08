/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Counterexample.Elimination

/-!

# Uniqueness of the full wait

The main theorem of our project.
-/

@[expose] public section

namespace Mahjong.Hand

theorem liveFullWait_unique (n : ℕ) (hn : n ≥ 2)
    (c : Hand n) (hc : c.IsLiveFullWait) : c = standardLiveFullWait n := by
  classical
  by_contra hne
  have hex : ∃ m, 2 ≤ m ∧ Counterexample.HasLiveCE m :=
    ⟨n, hn, c, hc, hne⟩
  let m := Nat.find hex
  obtain ⟨hm, d, hd⟩ := Nat.find_spec hex
  have hmin : ∀ k, 2 ≤ k → k < m → ¬ Counterexample.HasLiveCE k := by
    intro k hk hkm hcounterexample
    have := Nat.find_min' hex ⟨hk, hcounterexample⟩
    omega
  obtain ⟨k, hk, hk', hcounterexample⟩ :=
    liveFullWait_reduction hm hd
  have hmk : m ≤ k := Nat.find_min' hex ⟨hk, hcounterexample⟩
  have hm' : m ≤ 7 := hmk.trans hk'
  have hdmem :=
    Counterexample.mem_minimalCandidates_of_minimal hm hd hmin
  exact Counterexample.minimalCandidates_no_liveCE m hm hm' d hdmem hd

end Mahjong.Hand
