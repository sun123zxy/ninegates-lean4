/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Basic
public import Ninegates.Meldable.RequiredPatterns
public import Ninegates.Wait.Construction

/-! Explicit full-sidedness of `C` and `D`. The bottom fixed-class draw of `D`
uses the pair at paper rank four instead of a self-pair. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

variable {n : ℕ}

lemma full_one (order : 2 ≤ n) (r : Fin (3 * n - 2)) (low : r.val ≤ 1)
    (p q : Rank n) (left : p.val = 2) (right : q.val = 3 * n - 2) :
    IsFullWait (n + 1) (pair p + pair q + (segment 2 (3 * n - 1) + sequence r)) := by
  let s : Fin (3 * n - 2) → ℤ := fun j ↦ if j ∈ insert r RequiredSequences.third then 1 else 0
  have positive : 0 ≤ s := by intro j; dsimp [s]; split_ifs <;> norm_num
  have base : sequenceHand s = segment 2 (3 * n - 1) + sequence r :=
    RequiredSequences.sequenceHand_insert_third r low
  have class_p : rankClass p = 0 := by rw [rankClass_eq_zero_iff, left]
  have class_q : rankClass q = 2 := by rw [rankClass_eq_two_iff, right]; omega
  have row_p : RequiredSequences.row p = RequiredSequences.third := by
    apply RequiredSequences.row_eq_third p (by omega) (by omega)
  have row_q : RequiredSequences.row q = RequiredSequences.third := by
    ext j
    rw [RequiredSequences.mem_row_iff, RequiredSequences.mem_third_iff]
    unfold RequiredSequences.contains
    rw [right]
    omega
  apply isFullWait_of_sequence_rows p q 1 (by rw [class_p]; decide)
    (by rw [class_q]; decide) (by rw [class_p, class_q]; decide) positive
    (by rw [base])
  · rw [map_add, map_add, map_add, size_pair, size_pair, size_sequence,
      size_segment (by omega)]
    push_cast
    omega
  · intro j member
    rw [row_p] at member
    simp only [s, ite_eq_left (Finset.mem_insert_of_mem member)]
    norm_num
  · intro j member
    rw [row_q] at member
    simp only [s, ite_eq_left (Finset.mem_insert_of_mem member)]
    norm_num
  · intro i fixed
    have residue := (rankClass_eq_one_iff i).mp fixed
    have bound := i.isLt
    have choices : r.val = 0 ∨ r.val = 1 := by omega
    rcases choices with start | start
    · have sequential := sequential_segment_sub_single (n := n) (a := 0) (b := 3 * n - 2)
        (by omega) i (by omega) (by omega) (by omega) (by omega)
      refine ⟨i, ?_⟩
      have shape : pair p + pair q + (segment 2 (3 * n - 1) + sequence r) +
          single i - pair i = (segment 0 (3 * n - 2) - single i) + triplet p + triplet q := by
        rw [sequence_eq_segment]
        ext j
        have bound_j := j.isLt
        simp only [Pi.add_apply, Pi.sub_apply, segment_apply, single_apply, Fin.ext_iff,
          pair_apply, triplet_apply]
        simp only [left, right, start]
        split_ifs <;> omega
      change Meldable _
      rw [shape]
      exact (sequential.meldable.add_triplet p).add_triplet q
    · by_cases bottom : i.val = 0
      · let j : Rank n := ⟨3, by omega⟩
        have sequential := (sequential_segment (n := n) (a := 0) (b := 3)
          (by omega) (by omega) (by omega)).add
            (sequential_segment (a := 4) (b := 3 * n - 2) (by omega) (by omega) (by omega))
        refine ⟨j, ?_⟩
        have shape : pair p + pair q + (segment 2 (3 * n - 1) + sequence r) +
            single i - pair j = (segment 0 3 + segment 4 (3 * n - 2)) +
              triplet p + triplet q := by
          rw [sequence_eq_segment]
          ext k
          have bound_k := k.isLt
          simp only [Pi.add_apply, Pi.sub_apply, segment_apply, pair_apply, triplet_apply,
            single_apply, Fin.ext_iff]
          dsimp only [j]
          simp only [left, right, start, bottom]
          split_ifs <;> omega
        change Meldable _
        rw [shape]
        exact (sequential.meldable.add_triplet p).add_triplet q
      · have sequential := (sequential_segment (n := n) (a := 1) (b := 4)
          (by omega) (by omega) (by omega)).add
            (sequential_segment_sub_single (a := 3) (b := 3 * n - 2) (by omega) i
              (by omega) (by omega) (by omega) (by omega))
        refine ⟨i, ?_⟩
        have shape : pair p + pair q + (segment 2 (3 * n - 1) + sequence r) +
            single i - pair i = (segment 1 4 + (segment 3 (3 * n - 2) - single i)) +
              triplet p + triplet q := by
          rw [sequence_eq_segment]
          ext j
          have bound_j := j.isLt
          simp only [Pi.add_apply, Pi.sub_apply, segment_apply, pair_apply, triplet_apply,
            single_apply, Fin.ext_iff]
          simp only [left, right, start]
          split_ifs <;> omega
        change Meldable _
        rw [shape]
        exact (sequential.meldable.add_triplet p).add_triplet q

lemma C_full (order : 2 ≤ n) : IsFullWait (n + 1) (C n) := by
  let r : Fin (3 * n - 2) := ⟨0, by omega⟩
  let p : Rank n := ⟨2, by omega⟩
  let q : Rank n := ⟨3 * n - 2, by omega⟩
  have shape : C n = pair p + pair q + (segment 2 (3 * n - 1) + sequence r) := by
    rw [sequence_eq_segment]
    ext i
    have bound := i.isLt
    simp only [C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pair_apply, single_apply,
      Fin.ext_iff, segment_apply, singleAt_apply]
    dsimp only [r, p, q]
    split_ifs <;> omega
  rw [shape]
  exact full_one order r (by dsimp [r]; omega) p q rfl rfl

lemma D_full (order : 2 ≤ n) : IsFullWait (n + 1) (D n) := by
  let r : Fin (3 * n - 2) := ⟨1, by omega⟩
  let p : Rank n := ⟨2, by omega⟩
  let q : Rank n := ⟨3 * n - 2, by omega⟩
  have shape : D n = pair p + pair q + (segment 2 (3 * n - 1) + sequence r) := by
    rw [sequence_eq_segment]
    ext i
    have bound := i.isLt
    simp only [D, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pair_apply, single_apply,
      Fin.ext_iff, segment_apply, singleAt_apply]
    dsimp only [r, p, q]
    split_ifs <;> omega
  rw [shape]
  exact full_one order r (by dsimp [r]; omega) p q rfl rfl

end Mahjong.VirtualHand.Standard
