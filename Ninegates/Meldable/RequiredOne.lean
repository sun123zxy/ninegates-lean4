/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Required

/-! In fixed class one, one extra sequence outside the two required rows
forces those rows to coincide, fixing both pillars and all other sequences. -/

@[expose] public section

namespace Mahjong.VirtualHand.RequiredSequences

variable {n : ℕ}

def thirdStart (t : Fin (n - 1)) : Fin (3 * n - 2) := ⟨3 * t.val + 2, by have := t.isLt; omega⟩

@[simp]
lemma thirdStart_val (t : Fin (n - 1)) : (thirdStart t).val = 3 * t.val + 2 := rfl

lemma thirdStart_injective : Function.Injective (thirdStart (n := n)) := by
  intro a b equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp only [thirdStart_val] at values
  omega

def third : Finset (Fin (3 * n - 2)) := Finset.univ.image thirdStart

@[simp]
lemma card_third : (third (n := n)).card = n - 1 := by
  rw [third, Finset.card_image_of_injective _ thirdStart_injective]
  simp

lemma one_not_mem_row (q : Rank n) (q_class : q.val % 3 = 1) (later : 0 < q.val / 3)
    (j : Fin (3 * n - 2)) (one : j.val = 1) : j ∉ row q := by
  intro member
  obtain ⟨t, _, equal⟩ := Finset.mem_image.mp member
  have value := congrArg Fin.val equal
  simp only [start_val, q_class, one] at value
  split_ifs at value <;> omega

lemma blocks_one_of_rows_eq (order : 2 ≤ n) (p q : Rank n) (p_class : p.val % 3 = 2)
    (q_class : q.val % 3 = 1) (same : row p = row q) : p.val / 3 = 0 ∧ q.val / 3 = n - 1 := by
  have p_bound := p.isLt
  have q_bound := q.isLt
  have p_block : p.val / 3 = 0 := by
    by_contra positive
    have member : start p (⟨0, by omega⟩ : Fin (n - 1)) ∈ row q := by
      rw [← same]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    obtain ⟨t, _, equal⟩ := Finset.mem_image.mp member
    have values := congrArg Fin.val equal
    simp only [start_val, p_class, q_class] at values
    split_ifs at values <;> omega
  refine ⟨p_block, ?_⟩
  by_contra early
  have inside : q.val / 3 < n - 1 := by omega
  have member : start q (⟨q.val / 3, inside⟩ : Fin (n - 1)) ∈ row p := by
    rw [same]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  obtain ⟨t, _, equal⟩ := Finset.mem_image.mp member
  have values := congrArg Fin.val equal
  simp only [start_val, p_class, q_class, p_block, Nat.not_lt_zero, ite_false] at values
  split_ifs at values <;> omega

lemma row_eq_third (p : Rank n) (p_class : p.val % 3 = 2) (block : p.val / 3 = 0) :
    row p = third := by
  have equal : start p = thirdStart := by
    funext t
    apply Fin.ext
    simp only [start_val, thirdStart_val, p_class, block, Nat.not_lt_zero, ite_false, Nat.add_zero]
  rw [row, third, equal]

lemma coefficients_one (order : 2 ≤ n) {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (total : ∑ j, s j = (n : ℤ)) (p q : Rank n) (p_class : p.val % 3 = 2)
    (q_class : q.val % 3 = 1) (required_p : ∀ j ∈ row p, 1 ≤ s j)
    (required_q : ∀ j ∈ row q, 1 ≤ s j) (k : Fin (3 * n - 2))
    (outside : k ∉ row p ∪ row q) (extra : 1 ≤ s k) :
    p.val = 2 ∧ q.val = 3 * n - 2 ∧ s = fun j ↦ if j ∈ insert k third then 1 else 0 := by
  have same := rows_equal_of_extra order positive total p q required_p required_q k outside extra
  have blocks := blocks_one_of_rows_eq order p q p_class q_class same
  have positions : p.val = 2 ∧ q.val = 3 * n - 2 := by omega
  have row_p := row_eq_third p p_class blocks.1
  have not_in : k ∉ third := by intro member; apply outside; rw [← row_p] at member; simp [member]
  refine ⟨positions.1, positions.2, ?_⟩
  apply eq_indicator_of_sum_eq_card positive (insert k third)
  · intro j member
    rcases Finset.mem_insert.mp member with equal | inside
    · simpa only [equal] using extra
    · exact required_p j (by rwa [row_p])
  · rw [Finset.card_insert_of_notMem not_in, card_third, total]
    have cast : ((n - 1 : ℕ) : ℤ) + 1 = n := by omega
    simpa using cast.symm

end Mahjong.VirtualHand.RequiredSequences
