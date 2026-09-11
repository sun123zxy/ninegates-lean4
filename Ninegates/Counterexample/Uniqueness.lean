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
    (c : Hand n) (hc : c.IsLiveFullWait) : c = Standard.A n := by
  classical
  by_contra hne
  have hex : ∃ m, 2 ≤ m ∧ ∃ d : Hand m, IsLiveFullWait d ∧ d ≠ Standard.A m :=
    ⟨n, hn, c, hc, hne⟩
  let m := Nat.find hex
  obtain ⟨hm, d, hd⟩ := Nat.find_spec hex
  have hmin : ∀ k, 2 ≤ k → k < m →
      ¬ ∃ e : Hand k, IsLiveFullWait e ∧ e ≠ Standard.A k := by
    intro k hk hkm hcounterexample
    have := Nat.find_min' hex ⟨hk, hcounterexample⟩
    omega
  have hdmem :=
    Counterexample.mem_minimalCandidates_of_minimal hm hd hmin
  have hm' : m ≤ 7 := (Counterexample.mem_candidates_iff.mp hdmem).2.1
  exact Counterexample.minimalCandidates_no_liveCE m hm hm' d hdmem hd

end Mahjong.Hand
