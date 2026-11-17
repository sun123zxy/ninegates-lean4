/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Basic
public import Ninegates.Meldable.RequiredPatterns
public import Ninegates.Wait.Construction

/-! Explicit full-sidedness of the four fixed-class-two families. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

variable {n : ℕ}

lemma full_two (order : 2 ≤ n) (p q : Rank n)
    (left : p.val = 0 ∨ p.val = 3) (right : q.val = 3 * n - 4 ∨ q.val = 3 * n - 1) :
    IsFullWait (n + 1) (interiorOnes + triplet p + triplet q) := by
  let s : Fin (3 * n - 2) → ℤ := fun j ↦ if j ∈ RequiredSequences.row p ∪
    RequiredSequences.row q then 1 else 0
  have positive : 0 ≤ s := by intro j; dsimp [s]; split_ifs <;> norm_num
  have base := RequiredSequences.sequenceHand_union_two order p q left right
  have equal : interiorOnes + triplet p + triplet q = pair p + pair q + sequenceHand s := by
    rw [show sequenceHand s = interiorOnes + single p + single q from base]
    ext i
    simp only [Pi.add_apply, pair_apply, triplet_apply]
    ring
  have class_p : rankClass p = 1 := by rw [rankClass_eq_one_iff]; rcases left <;> omega
  have class_q : rankClass q = 0 := by rw [rankClass_eq_zero_iff]; rcases right <;> omega
  apply isFullWait_of_sequence_rows p q 2 (by rw [class_p]; decide)
    (by rw [class_q]; decide) (by rw [class_p, class_q]; decide) positive equal
  · rw [map_add, map_add, size_triplet, size_triplet, interiorOnes_eq_segment,
      size_segment (by omega)]
    push_cast
    omega
  · intro j member
    simp only [s, ite_eq_left (Finset.mem_union_left _ member)]
    norm_num
  · intro j member
    simp only [s, ite_eq_left (Finset.mem_union_right _ member)]
    norm_num
  · intro i fixed
    have residue := (rankClass_eq_two_iff i).mp fixed
    have bound := i.isLt
    have sequential : Sequential (interiorOnes - single i) := by
      rw [interiorOnes_eq_segment]
      exact sequential_segment_sub_single (by omega) i (by omega) (by omega)
        (by omega) (by omega)
    refine ⟨i, ?_⟩
    have melds := (sequential.meldable.add_triplet p).add_triplet q
    have shape : interiorOnes + triplet p + triplet q + single i - pair i =
        (interiorOnes - single i) + triplet p + triplet q := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, pair_apply]
      ring
    change Meldable (interiorOnes + triplet p + triplet q + single i - pair i)
    rw [shape]
    exact melds

lemma A_full (order : 2 ≤ n) : IsFullWait (n + 1) (A n) := by
  let p : Rank n := ⟨0, by omega⟩
  let q : Rank n := ⟨3 * n - 1, by omega⟩
  simpa only [A, p, q, triplet, ← singleAt_eq_single] using
    full_two order p q (Or.inl rfl) (Or.inr rfl)

lemma B_full (order : 2 ≤ n) : IsFullWait (n + 1) (B n) := by
  let p : Rank n := ⟨0, by omega⟩
  let q : Rank n := ⟨3 * n - 4, by omega⟩
  simpa only [B, p, q, triplet, ← singleAt_eq_single] using
    full_two order p q (Or.inl rfl) (Or.inl rfl)

lemma E_full (order : 2 ≤ n) : IsFullWait (n + 1) (E n) := by
  let p : Rank n := ⟨3, by omega⟩
  let q : Rank n := ⟨3 * n - 4, by omega⟩
  simpa only [E, p, q, triplet, ← singleAt_eq_single] using
    full_two order p q (Or.inr rfl) (Or.inl rfl)

end Mahjong.VirtualHand.Standard
