/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Coordinates

/-! Sequence placements and their uniqueness over the integers. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def sequenceHand : (Fin (3 * n - 2) → ℤ) →ₗ[ℤ] VirtualHand n where
  toFun s := ∑ j, s j • sequence j
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum, mul_assoc]

def VirtuallySequential (c : VirtualHand n) : Prop := ∃ s, sequenceHand s = c

def Sequential (c : VirtualHand n) : Prop := ∃ s, 0 ≤ s ∧ sequenceHand s = c

@[simp]
lemma sequenceHand_single (j : Fin (3 * n - 2)) (z : ℤ) :
    sequenceHand (Pi.single j z) = z • sequence j := by
  simp [sequenceHand, Pi.single_apply]

@[simp]
lemma Placement.toHand_no_triplets (s : Fin (3 * n - 2) → ℤ) :
    (⟨s, 0⟩ : Placement n).toHand = sequenceHand s := by
  simp [Placement.toHand, sequenceHand]

@[simp, grind =]
lemma sequenceHand_apply (s : Fin (3 * n - 2) → ℤ) (i : Rank n) :
    sequenceHand s i = coefficient s i.val + coefficient s ((i.val : ℤ) - 1) +
      coefficient s ((i.val : ℤ) - 2) := by
  simpa only [Placement.toHand_no_triplets, Pi.zero_apply, mul_zero, add_zero] using
    Placement.toHand_apply (⟨s, 0⟩ : Placement n) i

lemma Placement.toHand_eq (p : Placement n) :
    p.toHand = sequenceHand p.seqNum + (3 : ℤ) • p.tripNum := by
  ext i
  simp

lemma sequenceHand_injective : Function.Injective (sequenceHand (n := n)) := by
  intro s t equal
  apply coefficients_ext
  intro j
  let i : Rank n := ⟨j.val, by omega⟩
  have at_i := congrFun equal i
  simpa only [sequenceHand_apply] using at_i

lemma VirtuallySequential.unique {c : VirtualHand n} (h : VirtuallySequential c) :
    ∃! s, sequenceHand s = c := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs, fun t ht ↦ sequenceHand_injective (ht.trans hs.symm)⟩

lemma Sequential.meldable {c : VirtualHand n} (h : Sequential c) : Meldable c := by
  obtain ⟨s, nonnegative, equal⟩ := h
  exact ⟨⟨s, 0⟩, ⟨nonnegative, le_refl _⟩, by simpa using equal⟩

end Mahjong.VirtualHand
