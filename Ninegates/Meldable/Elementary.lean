/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.RemoveSequence
public import Ninegates.Meldable.Triplets

/-! A nonzero meldable hand contains an elementary meld that can be removed. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

@[simp]
lemma meldable_zero : Meldable (0 : VirtualHand n) :=
  ⟨⟨0, 0⟩, ⟨le_refl _, le_refl _⟩, by simp [Placement.toHand_eq]⟩

@[simp]
lemma meldable_triplet (i : Rank n) : Meldable (triplet i) :=
  ⟨⟨0, single i⟩, ⟨le_refl _, nonnegative_single i⟩, by simp [Placement.toHand_eq, triplet]⟩

@[simp]
lemma meldable_sequence (r : Fin (3 * n - 2)) : Meldable (sequence r) := by
  apply Sequential.meldable
  refine ⟨Pi.single r 1, ?_, by simp⟩
  intro j
  change 0 ≤ (Pi.single r 1 : Fin (3 * n - 2) → ℤ) j
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

lemma Meldable.exists_elementary_removal {c : VirtualHand n} (meldable : Meldable c)
    (nonzero : c ≠ 0) :
    (∃ i : Rank n, Meldable (c - triplet i)) ∨
      ∃ r : Fin (3 * n - 2), Meldable (c - sequence r) := by
  obtain ⟨p, ⟨positive, canonical, rfl⟩, _⟩ := meldable.unique_canonical
  by_cases triplets : ∃ i, 1 ≤ p.tripNum i
  · obtain ⟨i, available⟩ := triplets
    left
    refine ⟨i, (meldable.sub_triplet_iff i).mpr ?_⟩
    rwa [canonical.canonicalTriplet_eq]
  · by_cases sequences : ∃ r, 1 ≤ p.seqNum r
    · obtain ⟨r, available⟩ := sequences
      exact Or.inr ⟨r, (canonical.meldable_sub_sequence_iff positive.2 r).mpr (Or.inl available)⟩
    · have no_triplets : p.tripNum = 0 := by
        ext i
        have lower : 0 ≤ p.tripNum i := positive.2 i
        have upper : ¬1 ≤ p.tripNum i := fun h ↦ triplets ⟨i, h⟩
        change p.tripNum i = 0
        omega
      have no_sequences : p.seqNum = 0 := by
        ext r
        have lower : 0 ≤ p.seqNum r := positive.1 r
        have upper : ¬1 ≤ p.seqNum r := fun h ↦ sequences ⟨r, h⟩
        change p.seqNum r = 0
        omega
      exact (nonzero (by simp [Placement.toHand_eq, no_sequences, no_triplets])).elim

end Mahjong.VirtualHand
