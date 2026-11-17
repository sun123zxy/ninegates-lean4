/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Defs
public import Ninegates.Meldable.Basic

/-! Basic properties of the new paper's draw-pair relation. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m cap : ℕ} {c : VirtualHand n} {i j : Rank n}

lemma size_cast_of_wait_size (count : size c = 3 * (m : ℤ) + 1) :
    (size c : ZMod 3) = 1 := by
  rw [count]
  push_cast
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]

lemma IsFullWait.size_cast (full : IsFullWait m c) : (size c : ZMod 3) = 1 :=
  size_cast_of_wait_size full.2.1

lemma Winning.nonnegative (h : Winning m c) : Nonnegative c := by
  obtain ⟨j, remainder⟩ := h.2
  exact (nonnegative_pair j).trans (sub_nonneg.mp remainder.nonnegative)

@[simp]
lemma not_isFullWait_order_zero (m : ℕ) (c : VirtualHand 0) : ¬IsFullWait m c := by
  rintro ⟨_, count, _⟩
  have empty : size c = 0 := by simp [size]
  rw [empty] at count
  omega

lemma isWaitingTile_iff (hc : size c = 3 * (m : ℤ) + 1) :
    IsWaitingTile m c i ↔ ∃ j, DrawPair c i j := by
  simp [IsWaitingTile, Winning, DrawPair, hc, add_assoc]

lemma isFullWait_iff : IsFullWait m c ↔
    Nonnegative c ∧ size c = 3 * (m : ℤ) + 1 ∧ ∀ i, ∃ j, DrawPair c i j := by
  unfold IsFullWait
  constructor <;> rintro ⟨nonnegative, size, all⟩
  · exact ⟨nonnegative, size, fun i ↦ (isWaitingTile_iff size).mp (all i)⟩
  · exact ⟨nonnegative, size, fun i ↦ (isWaitingTile_iff size).mpr (all i)⟩

/-- Proposition `prp-draw-pair-congruence`, using one-based paper ranks. -/
lemma DrawPair.congruence (h : DrawPair c i j) :
    rankClass i + rankClass j = -(rankSum c : ZMod 3) := by
  have eq := (Meldable.virtuallyMeldable h).rankSum_cast
  simp only [map_sub, map_add, rankSum_single, rankSum_pair] at eq
  push_cast at eq
  change (rankSum c : ZMod 3) + rankClass i - 2 * rankClass j = 0 at eq
  have three : (3 : ZMod 3) * rankClass j = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  linear_combination eq + three

lemma DrawPair.pair_available (h : DrawPair c i j) (different : i ≠ j) : 2 ≤ c j := by
  have bound := Meldable.nonnegative h j
  simp [single, pair, Ne.symm different] at bound
  omega

lemma DrawPair.self_positive (h : DrawPair c i i) : 1 ≤ c i := by
  have bound := Meldable.nonnegative h i
  simp [single, pair] at bound
  omega

lemma isLiveFullWait_iff :
    IsLiveFullWait cap m c ↔ IsFullWait m c ∧ ∀ i, c i + 1 ≤ cap := by
  constructor
  · rintro ⟨full, live⟩
    refine ⟨full, ?_⟩
    intro i
    have bound := (live i).2 i
    simpa using bound
  · rintro ⟨full, bound⟩
    refine ⟨full, ?_⟩
    intro i
    refine ⟨full.1.add (nonnegative_single i), ?_⟩
    intro j
    have at_j := bound j
    simp only [Pi.add_apply, single]
    split <;> omega

end Mahjong.VirtualHand
