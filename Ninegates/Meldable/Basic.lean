/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Defs
public import Ninegates.Hand.Basic

/-! Tile counts, nonnegativity, and congruence obstructions for meld placements. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

@[simp]
lemma nonnegative_pair (i : Rank n) : Nonnegative (pair i) := by
  intro j
  exact mul_nonneg (by norm_num) (nonnegative_single i j)

@[simp]
lemma nonnegative_triplet (i : Rank n) : Nonnegative (triplet i) := by
  intro j
  exact mul_nonneg (by norm_num) (nonnegative_single i j)

@[simp]
lemma nonnegative_sequence (i : Fin (3 * n - 2)) : Nonnegative (sequence i) :=
  ((nonnegative_single _).add (nonnegative_single _)).add (nonnegative_single _)

namespace Placement

@[simp]
lemma size_toHand (p : Placement n) : size p.toHand = 3 * p.meldCount := by
  simp only [toHand, map_add, map_sum]
  simp_rw [map_smul, size_sequence, size_triplet]
  simp [meldCount, Finset.mul_sum, mul_comm, mul_add]

lemma nonnegative_toHand {p : Placement n} (hp : p.Nonnegative) :
    VirtualHand.Nonnegative p.toHand := by
  intro j
  simp only [toHand, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp.1 i) (nonnegative_sequence i j))
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp.2 i) (nonnegative_triplet i j))

lemma size_toHand_cast (p : Placement n) : (size p.toHand : ZMod 3) = 0 := by
  rw [size_toHand]
  push_cast
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]

lemma rankSum_toHand_cast (p : Placement n) : (rankSum p.toHand : ZMod 3) = 0 := by
  simp only [toHand, map_add, map_sum]
  simp_rw [map_smul, rankSum_sequence, rankSum_triplet]
  push_cast
  simp [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]

end Placement

lemma Meldable.nonnegative {c : VirtualHand n} (h : Meldable c) : Nonnegative c := by
  obtain ⟨p, hp, rfl⟩ := h
  exact Placement.nonnegative_toHand hp

lemma Meldable.virtuallyMeldable {c : VirtualHand n} (h : Meldable c) : VirtuallyMeldable c := by
  obtain ⟨p, _, rfl⟩ := h
  exact ⟨p, rfl⟩

lemma VirtuallyMeldable.size_cast {c : VirtualHand n} (h : VirtuallyMeldable c) :
    (size c : ZMod 3) = 0 := by
  obtain ⟨p, rfl⟩ := h
  exact p.size_toHand_cast

lemma VirtuallyMeldable.rankSum_cast {c : VirtualHand n} (h : VirtuallyMeldable c) :
    (rankSum c : ZMod 3) = 0 := by
  obtain ⟨p, rfl⟩ := h
  exact p.rankSum_toHand_cast

end Mahjong.VirtualHand
