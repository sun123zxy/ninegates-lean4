/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Basic
public import Ninegates.Meldable.Elementary
public import Ninegates.Wait.Add

/-! Minimality reduces to forbidding single elementary meld removals. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma IsFullWait.sub_of_decomposition (full : IsFullWait m c) {k : ℕ}
    {remainder removed meld : VirtualHand n} (smaller : IsFullWait k remainder)
    (equal : c = remainder + removed) (remaining : Meldable (removed - meld))
    (count : size meld = 3) : IsFullWait (m - 1) (c - meld) := by
  have positive_m : 0 < m := by have lower := full.meldCount_gt_order; omega
  have shape : c - meld = remainder + (removed - meld) := by rw [equal]; abel
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [shape]
    exact smaller.1.add remaining.nonnegative
  · rw [map_sub, full.2.1, count]
    omega
  · intro i
    obtain ⟨j, edge⟩ := (isFullWait_iff.mp smaller).2.2 i
    rw [shape]
    exact ⟨j, edge.add_meldable remaining⟩

lemma IsFullWait.minimal_of_no_elementary_removal (full : IsFullWait m c)
    (triplets : ∀ i, ¬IsFullWait (m - 1) (c - triplet i))
    (sequences : ∀ r, ¬IsFullWait (m - 1) (c - sequence r)) : IsMinimalFullWait m c := by
  refine ⟨full, ?_⟩
  intro k remainder removed smaller meldable equal
  by_contra nonzero
  rcases meldable.exists_elementary_removal nonzero with ⟨i, remaining⟩ | ⟨r, remaining⟩
  · exact triplets i (full.sub_of_decomposition smaller equal remaining (size_triplet i))
  · exact sequences r (full.sub_of_decomposition smaller equal remaining (size_sequence r))

lemma isMinimalFullWait_iff_no_elementary_removal : IsMinimalFullWait m c ↔
    IsFullWait m c ∧ (∀ i, ¬IsFullWait (m - 1) (c - triplet i)) ∧
      ∀ r, ¬IsFullWait (m - 1) (c - sequence r) := by
  constructor
  · intro minimal
    refine ⟨minimal.full, ?_, ?_⟩
    · intro i smaller
      have empty := minimal.minimal smaller (meldable_triplet i)
        (show c = (c - triplet i) + triplet i by abel)
      have count := congrArg size empty
      simp at count
    · intro r smaller
      have empty := minimal.minimal smaller (meldable_sequence r)
        (show c = (c - sequence r) + sequence r by abel)
      have count := congrArg size empty
      simp at count
  · rintro ⟨full, triplets, sequences⟩
    exact full.minimal_of_no_elementary_removal triplets sequences

/-- One critical draw with no usable canonical triplet prevents its removal. -/
lemma not_full_sub_triplet_of_canonical (k i : Rank n)
    (obstruction : ∀ q, DrawPair c i q → canonicalTriplet (c + single i - pair q) k = 0) :
    ¬IsFullWait m (c - triplet k) := by
  intro smaller
  obtain ⟨q, edge⟩ := (isFullWait_iff.mp smaller).2.2 i
  have shape : c - triplet k + single i - pair q =
      (c + single i - pair q) - triplet k := by abel
  have original : DrawPair c i q := by
    have extend := edge.add_meldable (meldable_triplet k)
    simpa only [sub_add_cancel] using extend
  have available := (original.sub_triplet_iff k).mp (shape ▸ edge)
  rw [obstruction q original] at available
  omega

/-- A critical draw must forbid both using the sequence and borrowing triplets. -/
lemma not_full_sub_sequence_of_canonical (r : Fin (3 * n - 2)) (i : Rank n)
    (obstruction : ∀ q, DrawPair c i q →
      canonicalSequence (c + single i - pair q) (r.val + 1) = 0 ∧
        ∃ k, sequence r k = 1 ∧ canonicalTriplet (c + single i - pair q) k = 0) :
    ¬IsFullWait m (c - sequence r) := by
  intro smaller
  obtain ⟨q, edge⟩ := (isFullWait_iff.mp smaller).2.2 i
  have shape : c - sequence r + single i - pair q =
      (c + single i - pair q) - sequence r := by abel
  have original : DrawPair c i q := by
    have extend := edge.add_meldable (meldable_sequence r)
    simpa only [sub_add_cancel] using extend
  obtain ⟨zero, k, covered, absent⟩ := obstruction q original
  rcases (original.sub_sequence_iff r).mp (shape ▸ edge) with available | borrow
  · rw [zero] at available
    omega
  · have available := borrow k
    rw [covered, absent] at available
    norm_num at available

end Mahjong.VirtualHand
