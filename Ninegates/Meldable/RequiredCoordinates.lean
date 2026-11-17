/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Required

/-! Arithmetic membership in a required row, including its zero extension.
These formulas identify the forced placements with the standard hand vectors. -/

@[expose] public section

namespace Mahjong.VirtualHand.RequiredSequences

variable {n : ℕ}

abbrev contains (i : Rank n) (k : ℤ) : Prop :=
  ((i.val % 3 : ℤ) + 1 ≤ k ∧ k < i.val ∧ (k - (i.val % 3 + 1)) % 3 = 0) ∨
    ((i.val : ℤ) ≤ k ∧ k < 3 * (n - 1) + i.val % 3 ∧ (k - i.val % 3) % 3 = 0)

lemma mem_row_iff (i : Rank n) (j : Fin (3 * n - 2)) : j ∈ row i ↔ contains i j.val := by
  have bound := i.isLt
  constructor
  · intro member
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp member
    have t_bound := t.isLt
    unfold contains
    simp only [start_val]
    split_ifs <;> omega
  · intro member
    rcases member with left | right
    · let t : Fin (n - 1) := ⟨(j.val - (i.val % 3 + 1)) / 3, by omega⟩
      apply Finset.mem_image.mpr
      refine ⟨t, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only [start_val]
      dsimp only [t]
      split_ifs <;> omega
    · let t : Fin (n - 1) := ⟨(j.val - i.val % 3) / 3, by omega⟩
      apply Finset.mem_image.mpr
      refine ⟨t, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only [start_val]
      dsimp only [t]
      split_ifs <;> omega

lemma coefficient_union (p q : Rank n) (k : ℤ) :
    coefficient (fun j ↦ if j ∈ row p ∪ row q then (1 : ℤ) else 0) k =
      if contains p k ∨ contains q k then 1 else 0 := by
  have p_bound := p.isLt
  have q_bound := q.isLt
  by_cases inside : 0 ≤ k ∧ k < (3 * n - 2 : ℕ)
  · rw [coefficient, dite_eq_left inside]
    simp only [Finset.mem_union, mem_row_iff]
    have index : (((k.toNat : ℕ) : ℤ)) = k := by omega
    simp only [index]
  · rw [coefficient, dite_eq_right inside]
    unfold contains
    split_ifs <;> omega

/-- Containing the required row is sufficient for every same-class move. -/
lemma moves_of_row {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s) (p : Rank n)
    (required : ∀ j ∈ row p, 1 ≤ s j) (i : Rank n) (same : rankClass i = rankClass p) :
    Sequential (moveTile (sequenceHand s) p i) := by
  have congruent := (rankClass_eq_iff i p).mp same
  have p_bound := p.isLt
  have i_bound := i.isLt
  by_cases order : p.val ≤ i.val
  · apply (sequential_moveTile_right_iff positive p i order).mpr
    refine ⟨same.symm, ?_⟩
    intro r lower upper residue
    apply required r
    rw [mem_row_iff]
    unfold contains
    omega
  · apply (sequential_moveTile_left_iff positive p i (by omega)).mpr
    refine ⟨same.symm, ?_⟩
    intro r lower upper residue
    apply required r
    rw [mem_row_iff]
    unfold contains
    omega

end Mahjong.VirtualHand.RequiredSequences
