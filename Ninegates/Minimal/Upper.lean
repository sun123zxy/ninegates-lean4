/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Basic
public import Ninegates.Meldable.Large
public import Ninegates.Wait.Add

/-! A rank of multiplicity at least nine supplies a removable triplet for
every draw. Minimal full waits therefore have multiplicities at most eight. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma IsFullWait.sub_triplet_of_nine (full : IsFullWait m c) (i : Rank n) (large : 9 ≤ c i) :
    IsFullWait (m - 1) (c - triplet i) := by
  have positive_m : 0 < m := by have lower := full.meldCount_gt_order; omega
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have positive : 0 ≤ c j := full.1 j
    change 0 ≤ c j - triplet i j
    simp only [triplet_apply, single_apply]
    split_ifs with same
    · subst j
      omega
    · omega
  · rw [map_sub, full.2.1, size_triplet]
    omega
  · intro p
    obtain ⟨q, edge⟩ := (isFullWait_iff.mp full).2.2 p
    have remainder_large : 7 ≤ (c + single p - pair q) i := by
      have positive : 0 ≤ single p i := nonnegative_single p i
      have pair_bound : pair q i ≤ 2 := by
        simp only [pair_apply, single_apply]
        split_ifs <;> norm_num
      change 7 ≤ c i + single p i - pair q i
      omega
    have removed := edge.sub_triplet_of_seven i remainder_large
    refine ⟨q, ?_⟩
    change Meldable (c - triplet i + single p - pair q)
    have shape : c - triplet i + single p - pair q = (c + single p - pair q) - triplet i := by
      abel
    rw [shape]
    exact removed

lemma IsMinimalFullWait.bounded (minimal : IsMinimalFullWait m c) : Bounded 8 c := by
  refine ⟨minimal.full.1, ?_⟩
  intro i
  by_contra large
  have removable := minimal.full.sub_triplet_of_nine i (by omega)
  have triplet_meldable : Meldable (triplet i) := by
    refine ⟨⟨0, single i⟩, ⟨le_refl _, nonnegative_single i⟩, ?_⟩
    simp [Placement.toHand_eq, triplet]
  have empty := minimal.minimal removable triplet_meldable (show c = c - triplet i + triplet i by
    abel)
  have count := congrArg size empty
  simp at count

lemma IsMinimalFullWait.meldCount_lt_eight_order (minimal : IsMinimalFullWait m c) : m < 8 * n := by
  have upper := minimal.bounded.size_le
  rw [minimal.full.2.1] at upper
  omega

end Mahjong.VirtualHand
