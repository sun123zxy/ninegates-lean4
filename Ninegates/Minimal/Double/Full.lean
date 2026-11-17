/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Periodic
public import Ninegates.Meldable.SequentialMoving
public import Ninegates.Hand.Size
public import Ninegates.Wait.Graph

/-! The paper's lower-bound family `(3,2,...,2)` is a full-sided `(n,2n)` wait. -/

@[expose] public section

namespace Mahjong.VirtualHand.DoubleWait

def hand (n : ℕ) : VirtualHand n := (fun _ ↦ 2) + singleAt 0

@[grind =]
lemma hand_apply {n : ℕ} (i : Rank n) : hand n i = if i.val = 0 then 3 else 2 := by
  simp only [hand, Pi.add_apply, singleAt_apply]
  split_ifs <;> norm_num

lemma hand_eq {n : ℕ} (first : Rank n) (zero : first.val = 0) :
    hand n = (fun _ ↦ 2) + single first := by
  rw [hand, ← singleAt_eq_single, zero]

lemma size_hand {n : ℕ} (positive : 0 < n) : size (hand n) = 6 * (n : ℤ) + 1 := by
  rw [hand, map_add, size_const, size_singleAt (by omega)]
  ring

lemma sequential_twos {n : ℕ} : Sequential (fun _ : Rank n ↦ 2) := by
  refine ⟨fun j ↦ Periodic.value 2 0 0 j.val, ?_, Periodic.sequenceHand_twos⟩
  intro j
  change 0 ≤ Periodic.value 2 0 0 j.val
  unfold Periodic.value
  split_ifs <;> norm_num

lemma fixedClass_hand {n : ℕ} (positive : 0 < n) : fixedClass (hand n) = 1 := by
  let first : Rank n := ⟨0, by omega⟩
  have weighted := (sequential_twos (n := n)).meldable.virtuallyMeldable.rankSum_cast
  rw [hand_eq first rfl, fixedClass, map_add, rankSum_single]
  push_cast
  rw [weighted]
  rfl

lemma full {n : ℕ} (positive : 0 < n) : IsFullWait (2 * n) (hand n) := by
  let first : Rank n := ⟨0, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  let second : Rank n := ⟨1, by omega⟩
  apply isFullWait_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change 0 ≤ hand n i
    rw [hand_apply]
    split_ifs <;> norm_num
  · rw [size_hand positive]
    push_cast
    ring
  · intro i
    have bound := i.isLt
    have residues : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
    rcases residues with residue | residue | residue
    · have moved : Sequential (moveTile (fun _ : Rank n ↦ 2) first i) := by
        rw [← Periodic.sequenceHand_twos]
        apply (sequential_moveTile_right_iff (s := fun j ↦ Periodic.value 2 0 0 j.val)
          (by
            intro j
            change 0 ≤ Periodic.value 2 0 0 j.val
            unfold Periodic.value
            split_ifs <;> norm_num) first i
          (by dsimp [first]; omega)).mpr
        refine ⟨?_, ?_⟩
        · rw [rankClass_eq_iff]
          dsimp only [first]
          omega
        · intro r lower upper congruent
          have at_r : (r.val : ℤ) % 3 = 0 := by dsimp [first] at congruent; omega
          simp [Periodic.value, at_r]
      refine ⟨first, ?_⟩
      have shape : hand n + single i - pair first = moveTile (fun _ : Rank n ↦ 2) first i := by
        rw [hand_eq first rfl]
        ext j
        simp only [moveTile, Pi.add_apply, Pi.sub_apply, pair_apply]
        ring
      change Meldable _
      rw [shape]
      exact moved.meldable
    · have intervals := ((sequential_segment (n := n) (a := 1) (b := i.val)
        (by omega) (by omega) (by omega)).add
          (sequential_segment (a := i.val + 1) (b := 3 * n - 1)
            (by omega) (by omega) (by omega))).smul (z := 2) (by norm_num)
      refine ⟨last, ?_⟩
      have shape : hand n + single i - pair last =
          (2 : ℤ) • (segment 1 i.val + segment (i.val + 1) (3 * n - 1)) +
            triplet first + triplet i := by
        ext j
        have bound_j := j.isLt
        simp only [hand_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          pair_apply, triplet_apply, single_apply, Fin.ext_iff, segment_apply]
        dsimp only [first, last]
        split_ifs <;> omega
      change Meldable _
      rw [shape]
      exact (intervals.meldable.add_triplet first).add_triplet i
    · have intervals := ((sequential_segment (n := n) (a := 2) (b := i.val)
        (by omega) (by omega) (by omega)).add
          (sequential_segment (a := i.val + 1) (b := 3 * n)
            (by omega) (by omega) (by omega))).smul (z := 2) (by norm_num)
      refine ⟨second, ?_⟩
      have shape : hand n + single i - pair second =
          (2 : ℤ) • (segment 2 i.val + segment (i.val + 1) (3 * n)) +
            triplet first + triplet i := by
        ext j
        have bound_j := j.isLt
        simp only [hand_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          pair_apply, triplet_apply, single_apply, Fin.ext_iff, segment_apply]
        dsimp only [first, second]
        split_ifs <;> omega
      change Meldable _
      rw [shape]
      exact (intervals.meldable.add_triplet first).add_triplet i

lemma live {n : ℕ} (positive : 0 < n) : IsLiveFullWait 4 (2 * n) (hand n) := by
  apply isLiveFullWait_iff.mpr
  refine ⟨full positive, ?_⟩
  intro i
  rw [hand_apply]
  split_ifs <;> norm_num

end Mahjong.VirtualHand.DoubleWait
