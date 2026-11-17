/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.RequiredCoordinates
public import Ninegates.Wait.Graph

/-! Construct full waits from the two required rows and explicit winning
decompositions for draws in the remaining class. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma drawPair_of_sequence_move {s : Fin (3 * n - 2) → ℤ} (p q i : Rank n)
    (equal : c = pair p + pair q + sequenceHand s)
    (move : Sequential (moveTile (sequenceHand s) p i)) : DrawPair c i q := by
  have melds := move.meldable.add_triplet p
  have shape : c + single i - pair q = moveTile (sequenceHand s) p i + triplet p := by
    rw [equal]
    ext j
    simp only [moveTile, Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply]
    ring
  change Meldable (c + single i - pair q)
  rw [shape]
  exact melds

lemma isFullWait_of_sequence_rows (p q : Rank n) (r : ZMod 3)
    (different_p : r ≠ rankClass p) (different_q : r ≠ rankClass q)
    (different : rankClass p ≠ rankClass q) {s : Fin (3 * n - 2) → ℤ}
    (positive : 0 ≤ s) (equal : c = pair p + pair q + sequenceHand s)
    (count : size c = 3 * (m : ℤ) + 1)
    (required_p : ∀ j ∈ RequiredSequences.row p, 1 ≤ s j)
    (required_q : ∀ j ∈ RequiredSequences.row q, 1 ≤ s j)
    (fixed : ∀ i, rankClass i = r → ∃ j, DrawPair c i j) : IsFullWait m c := by
  apply isFullWait_iff.mpr
  refine ⟨?_, count, ?_⟩
  · rw [equal]
    exact ((nonnegative_pair p).add (nonnegative_pair q)).add
      (Sequential.meldable ⟨s, positive, rfl⟩).nonnegative
  · intro i
    rcases three_classes_exhaust r (rankClass p) (rankClass q) different_p different_q
      different (rankClass i) with fixed_i | left | right
    · exact fixed i fixed_i
    · exact ⟨q, drawPair_of_sequence_move p q i equal
        (RequiredSequences.moves_of_row positive p required_p i left)⟩
    · have swapped : c = pair q + pair p + sequenceHand s := by rw [equal]; abel
      exact ⟨p, drawPair_of_sequence_move q p i swapped
        (RequiredSequences.moves_of_row positive q required_q i right)⟩

end Mahjong.VirtualHand
