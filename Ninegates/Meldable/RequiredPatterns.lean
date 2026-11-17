/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.RequiredCoordinates
public import Ninegates.Meldable.RequiredOne
public import Ninegates.Hand.Interior
public import Ninegates.Meldable.Segment

/-! Coordinate forms of the two forced sequence templates. -/

@[expose] public section

namespace Mahjong.VirtualHand.RequiredSequences

variable {n : ℕ}

lemma contains_union_two (order : 2 ≤ n) (p q : Rank n)
    (left : p.val = 0 ∨ p.val = 3) (right : q.val = 3 * n - 4 ∨ q.val = 3 * n - 1)
    (k : ℤ) : contains p k ∨ contains q k ↔
      (3 ≤ k ∧ k + 3 ≤ 3 * n - 3 ∧ (k - 3) % 3 = 0) ∨
        k = p.val / 3 ∨ k = q.val - (if q.val = 3 * n - 1 then 2 else 0) := by
  unfold contains
  rcases left with left | left <;> rcases right with right | right
  all_goals rw [left, right]; split_ifs <;> omega

lemma sequenceHand_union_two (order : 2 ≤ n) (p q : Rank n)
    (left : p.val = 0 ∨ p.val = 3) (right : q.val = 3 * n - 4 ∨ q.val = 3 * n - 1) :
    sequenceHand (fun j ↦ if j ∈ row p ∪ row q then 1 else 0) =
      interiorOnes + single p + single q := by
  let a : Fin (3 * n - 2) := ⟨p.val / 3, by rcases left with h | h <;> omega⟩
  let b : Fin (3 * n - 2) :=
    ⟨q.val - (if q.val = 3 * n - 1 then 2 else 0), by
      rcases right with h | h <;> split_ifs <;> omega⟩
  have coefficients : (fun j ↦ if j ∈ row p ∪ row q then (1 : ℤ) else 0) =
      (fun j ↦ Segment.starts 3 (3 * n - 3) j.val) + Pi.single a 1 + Pi.single b 1 := by
    ext j
    rw [← coefficient_fin (fun r ↦ if r ∈ row p ∪ row q then (1 : ℤ) else 0) j,
      coefficient_union]
    simp only [contains_union_two order p q left right]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff, Segment.starts]
    dsimp only [a, b]
    rcases left with left | left <;> rcases right with right | right
    all_goals simp only [left, right]; split_ifs <;> omega
  have end_cast : ((3 * n - 3 : ℕ) : ℤ) = 3 * (n : ℤ) - 3 := by omega
  rw [← end_cast] at coefficients
  have middle := Segment.sequenceHand_starts (n := n) (a := 3) (b := 3 * n - 3)
    (by omega) (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at middle
  rw [coefficients, map_add, map_add, middle,
    sequenceHand_single, sequenceHand_single, one_smul, one_smul]
  rw [sequence_eq_segment, sequence_eq_segment]
  ext i
  have bound := i.isLt
  simp only [Pi.add_apply, segment_apply, interiorOnes_apply, single_apply, Fin.ext_iff]
  dsimp only [a, b]
  rcases left with left | left <;> rcases right with right | right
  all_goals simp only [left, right]; split_ifs <;> omega

lemma mem_third_iff (j : Fin (3 * n - 2)) :
    j ∈ third ↔ 2 ≤ j.val ∧ j.val < 3 * n - 3 ∧ j.val % 3 = 2 := by
  constructor
  · intro member
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp member
    have bound := t.isLt
    simp only [thirdStart_val]
    omega
  · rintro ⟨lower, upper, residue⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨j.val / 3, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only [thirdStart_val]
    omega

lemma sequenceHand_insert_third (r : Fin (3 * n - 2)) (low : r.val ≤ 1) :
    sequenceHand (fun j ↦ if j ∈ insert r third then 1 else 0) =
      segment 2 (3 * n - 1) + sequence r := by
  have base : sequenceHand (n := n) (fun j ↦ if j ∈ third then (1 : ℤ) else 0) =
      segment 2 (3 * n - 1) := by
    ext i
    have bound := i.isLt
    have coefficient_third (k : ℤ) :
        coefficient (fun j : Fin (3 * n - 2) ↦ if j ∈ third then (1 : ℤ) else 0) k =
          if 2 ≤ k ∧ k < 3 * n - 3 ∧ (k - 2) % 3 = 0 then 1 else 0 := by
      by_cases inside : 0 ≤ k ∧ k < (3 * n - 2 : ℕ)
      · rw [coefficient, dite_eq_left inside]
        simp only [mem_third_iff]
        split_ifs <;> omega
      · rw [coefficient, dite_eq_right inside]
        split_ifs <;> omega
    simp only [sequenceHand_apply, coefficient_third, segment_apply]
    split_ifs <;> omega
  have different : r ∉ third := by
    rw [mem_third_iff]
    omega
  have coefficients : (fun j ↦ if j ∈ insert r third then (1 : ℤ) else 0) =
      (fun j ↦ if j ∈ third then (1 : ℤ) else 0) + Pi.single r 1 := by
    ext j
    simp only [Finset.mem_insert, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp_all
  rw [coefficients, map_add, base, sequenceHand_single, one_smul]

end Mahjong.VirtualHand.RequiredSequences
