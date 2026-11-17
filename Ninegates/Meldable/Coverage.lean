/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Scan

/-! A boundary-sensitive bound on the tiles used by canonical sequences.
This is the threshold hand in the paper's abundance proposition. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def abundanceThreshold : VirtualHand n := fun i ↦
  if i.val = 0 ∨ i.val + 1 = 3 * n then 2
  else if i.val = 1 ∨ i.val + 2 = 3 * n then 4 else 6

@[grind =]
lemma abundanceThreshold_apply (i : Rank n) : abundanceThreshold i =
    if i.val = 0 ∨ i.val + 1 = 3 * n then 2
    else if i.val = 1 ∨ i.val + 2 = 3 * n then 4 else 6 := rfl

lemma abundanceThreshold_bounds (i : Rank n) :
    2 ≤ abundanceThreshold i ∧ abundanceThreshold i ≤ 6 := by
  unfold abundanceThreshold
  split_ifs <;> norm_num

lemma abundanceThreshold_orderOne : (abundanceThreshold : VirtualHand 1) = ![2, 4, 2] := by
  ext i
  fin_cases i <;> norm_num [abundanceThreshold]

lemma Placement.Canonic.sequenceHand_le_threshold {p : Placement n} (canonical : p.Canonic) :
    sequenceHand p.seqNum ≤ abundanceThreshold := by
  intro i
  have bound := i.isLt
  have current := canonical.coefficient_bounds i.val
  have previous := canonical.coefficient_bounds ((i.val : ℤ) - 1)
  have older := canonical.coefficient_bounds ((i.val : ℤ) - 2)
  have left_one : i.val = 0 → coefficient p.seqNum ((i.val : ℤ) - 1) = 0 := by
    intro first
    exact coefficient_of_neg _ (by omega)
  have left_two : i.val ≤ 1 → coefficient p.seqNum ((i.val : ℤ) - 2) = 0 := by
    intro first
    exact coefficient_of_neg _ (by omega)
  have right_one : 3 * n - 2 ≤ i.val → coefficient p.seqNum i.val = 0 := by
    intro last
    exact coefficient_of_ge _ (by omega)
  have right_two : i.val + 1 = 3 * n → coefficient p.seqNum ((i.val : ℤ) - 1) = 0 := by
    intro last
    exact coefficient_of_ge _ (by omega)
  rw [sequenceHand_apply, abundanceThreshold_apply]
  have current_le : coefficient p.seqNum (i.val : ℤ) ≤ 2 := by omega
  have previous_le : coefficient p.seqNum ((i.val : ℤ) - 1) ≤ 2 := by omega
  have older_le : coefficient p.seqNum ((i.val : ℤ) - 2) ≤ 2 := by omega
  split_ifs with boundary near
  · rcases boundary with first | last
    · rw [left_one first, left_two (by omega)]
      simpa using current_le
    · rw [right_one (by omega), right_two last]
      simpa using older_le
  · rcases near with first | last
    · rw [left_two (by omega)]
      linarith
    · rw [right_one (by omega)]
      linarith
  · linarith

lemma VirtuallyMeldable.meldable_of_ge_threshold {c : VirtualHand n}
    (virtual : VirtuallyMeldable c) (large : ∀ i, abundanceThreshold i - 2 ≤ c i) :
    Meldable c := by
  obtain ⟨p, ⟨canonical, equal⟩, _⟩ := virtual.unique_canonical
  rw [← equal, canonical.meldable_iff_tripNum_nonnegative]
  intro i
  change 0 ≤ p.tripNum i
  have upper := canonical.sequenceHand_le_threshold i
  have lower := large i
  rw [← equal, Placement.toHand_eq] at lower
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at lower
  have triplet_bound : -2 ≤ 3 * p.tripNum i := by linarith [upper, lower]
  omega

/-- The abundance estimate also applies to a single coordinate. -/
lemma VirtuallyMeldable.canonicalTriplet_nonnegative_of_threshold {c : VirtualHand n}
    (virtual : VirtuallyMeldable c) (i : Rank n) (large : abundanceThreshold i - 2 ≤ c i) :
    0 ≤ canonicalTriplet c i := by
  obtain ⟨p, ⟨canonical, equal⟩, _⟩ := virtual.unique_canonical
  rw [← equal, canonical.canonicalTriplet_eq]
  have upper := canonical.sequenceHand_le_threshold i
  rw [← equal, Placement.toHand_eq] at large
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at large
  have triplet_bound : -2 ≤ 3 * p.tripNum i := by linarith [upper, large]
  omega

end Mahjong.VirtualHand
