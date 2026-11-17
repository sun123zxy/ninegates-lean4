/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Coverage
public import Ninegates.Wait.Classes
public import Ninegates.Wait.OrderOne

/-! Above the threshold hand, every congruence-permitted draw-pair edge exists. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma drawPair_of_abundant (count : (size c : ZMod 3) = 1)
    (large : abundanceThreshold ≤ c) (i j : Rank n)
    (congruent : rankClass i + rankClass j = -(rankSum c : ZMod 3)) : DrawPair c i j := by
  apply ((virtuallyMeldable_draw_iff count i j).mpr congruent).meldable_of_ge_threshold
  intro k
  have floor : abundanceThreshold k ≤ c k := large k
  have nonnegative : 0 ≤ single i k := nonnegative_single i k
  have pair_bound : pair j k ≤ 2 := by
    simp only [pair_apply, single_apply]
    split_ifs <;> norm_num
  change abundanceThreshold k - 2 ≤ c k + single i k - pair j k
  linarith

lemma isFullWait_of_abundant (order : 0 < n) (large : abundanceThreshold ≤ c)
    (count : size c = 3 * (m : ℤ) + 1) : IsFullWait m c := by
  have residue := size_cast_of_wait_size count
  apply isFullWait_iff.mpr
  refine ⟨?_, count, ?_⟩
  · intro i
    change 0 ≤ c i
    have floor : abundanceThreshold i ≤ c i := large i
    have lower := (abundanceThreshold_bounds i).1
    linarith
  · intro i
    obtain ⟨j, class_j⟩ := exists_rankClass order (-(rankSum c : ZMod 3) - rankClass i)
    exact ⟨j, drawPair_of_abundant residue large i j (by rw [class_j]; ring)⟩

/-- At order one, two copies at each rank suffice for every permitted edge. -/
lemma drawPair_orderOne_of_two {c : VirtualHand 1} (count : (size c : ZMod 3) = 1)
    (large : ∀ i, 2 ≤ c i) (i j : Rank 1)
    (congruent : rankClass i + rankClass j = -(rankSum c : ZMod 3)) : DrawPair c i j :=
  OrderOne.drawPair_of_threshold count
    (fun k ↦ (OrderOne.pairThreshold_bounds _ k).2.trans (large k)) i j congruent

lemma isFullWait_orderOne_of_two {c : VirtualHand 1} (large : ∀ i, 2 ≤ c i)
    (count : size c = 3 * (m : ℤ) + 1) : IsFullWait m c := by
  apply (OrderOne.full_iff c).mpr
  exact ⟨count, fun i ↦ (OrderOne.pairThreshold_bounds _ i).2.trans (large i)⟩

end Mahjong.VirtualHand
