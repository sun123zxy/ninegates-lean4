/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Scan

/-! Removing a sequence either uses its canonical coefficient, or borrows
one triplet from each of its three ranks and returns two sequences. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

namespace Placement

def removeSequence (p : Placement n) (r : Fin (3 * n - 2)) : Placement n :=
  if p.seqNum r = 0 then ⟨p.seqNum + Pi.single r 2, p.tripNum - sequence r⟩
  else ⟨p.seqNum - Pi.single r 1, p.tripNum⟩

@[simp]
lemma toHand_removeSequence (p : Placement n) (r : Fin (3 * n - 2)) :
    (p.removeSequence r).toHand = p.toHand - sequence r := by
  by_cases zero : p.seqNum r = 0
  · simp only [removeSequence, zero, ite_true, toHand_eq]
    rw [map_add, sequenceHand_single, smul_sub]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [removeSequence, zero, ite_false, toHand_eq]
    rw [map_sub, sequenceHand_single, one_smul]
    abel

lemma Canonic.removeSequence {p : Placement n} (canonical : p.Canonic)
    (r : Fin (3 * n - 2)) : (p.removeSequence r).Canonic := by
  intro s
  have original := canonical s
  have source := canonical r
  by_cases zero : p.seqNum r = 0
  · simp only [Placement.removeSequence, zero, ite_true, Pi.add_apply, Pi.single_apply]
    split_ifs with same
    · subst s
      rw [zero]
      norm_num
    · simpa using original
  · simp only [Placement.removeSequence, zero, ite_false, Pi.sub_apply, Pi.single_apply]
    split_ifs with same
    · subst s
      omega
    · simpa using original

lemma Canonic.meldable_sub_sequence_iff {p : Placement n} (canonical : p.Canonic)
    (positive : 0 ≤ p.tripNum) (r : Fin (3 * n - 2)) :
    Meldable (p.toHand - sequence r) ↔ 1 ≤ p.seqNum r ∨ sequence r ≤ p.tripNum := by
  rw [← toHand_removeSequence, (canonical.removeSequence r).meldable_iff_tripNum_nonnegative]
  by_cases zero : p.seqNum r = 0
  · simp only [Placement.removeSequence, zero, ite_true, not_le.mpr (by norm_num : (0 : ℤ) < 1),
      false_or]
    exact sub_nonneg
  · have available : 1 ≤ p.seqNum r := by have lower := (canonical r).1; omega
    simp only [Placement.removeSequence, zero, ite_false, available, true_or]
    exact iff_true_intro positive

end Placement

lemma Meldable.sub_sequence_iff {c : VirtualHand n} (meldable : Meldable c)
    (r : Fin (3 * n - 2)) : Meldable (c - sequence r) ↔
      1 ≤ canonicalSequence c (r.val + 1) ∨ sequence r ≤ canonicalTriplet c := by
  obtain ⟨p, ⟨positive, canonical, equal⟩, _⟩ := meldable.unique_canonical
  have sequences : canonicalSequence c (r.val + 1) = p.seqNum r := by
    rw [← equal, canonical.canonicalSequence_eq (r.val + 1) (by omega)]
    have index : ((r.val + 1 : ℕ) : ℤ) - 1 = r.val := by omega
    rw [index, coefficient_fin]
  have triplets : canonicalTriplet c = p.tripNum := by
    ext i
    rw [← equal, canonical.canonicalTriplet_eq]
  rw [sequences, triplets, ← equal]
  exact canonical.meldable_sub_sequence_iff positive.2 r

end Mahjong.VirtualHand
