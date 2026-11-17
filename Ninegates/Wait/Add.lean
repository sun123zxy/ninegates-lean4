/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Triplets
public import Ninegates.Meldable.Size
public import Ninegates.Wait.Basic

/-! Adding a meldable hand preserves every draw-pair edge and full-sidedness. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m k : ℕ} {c d : VirtualHand n} {i j : Rank n}

lemma DrawPair.add_meldable (edge : DrawPair c i j) (melds : Meldable d) :
    DrawPair (c + d) i j := by
  change Meldable (c + d + single i - pair j)
  have shape : c + d + single i - pair j = (c + single i - pair j) + d := by abel
  rw [shape]
  exact edge.add melds

lemma IsFullWait.add_meldable (full : IsFullWait m c) (melds : Meldable d)
    (count : size d = 3 * (k : ℤ)) : IsFullWait (m + k) (c + d) := by
  apply isFullWait_iff.mpr
  refine ⟨full.1.add melds.nonnegative, ?_, ?_⟩
  · rw [map_add, full.2.1, count]
    push_cast
    ring
  · intro i
    obtain ⟨j, edge⟩ := (isFullWait_iff.mp full).2.2 i
    exact ⟨j, edge.add_meldable melds⟩

lemma IsFullWait.add_triplet (full : IsFullWait m c) (i : Rank n) :
    IsFullWait (m + 1) (c + triplet i) :=
  full.add_meldable (by exact ⟨⟨0, single i⟩,
    ⟨le_refl _, nonnegative_single i⟩, by simp [Placement.toHand_eq, triplet]⟩) (size_triplet i)

lemma IsFullWait.add_sequence (full : IsFullWait m c) (i : Fin (3 * n - 2)) :
    IsFullWait (m + 1) (c + sequence i) :=
  full.add_meldable (Sequential.meldable ⟨Pi.single i 1, by
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num, by simp⟩) (size_sequence i)

end Mahjong.VirtualHand
