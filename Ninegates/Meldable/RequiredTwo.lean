/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Required

/-! Required rows when the fixed class is two. Their overlap exhausts the
middle starts divisible by three, forcing the four possible pillar positions. -/

@[expose] public section

namespace Mahjong.VirtualHand.RequiredSequences

variable {n : ℕ}

def middleStart (t : Fin (n - 2)) : Fin (3 * n - 2) :=
  ⟨3 * (t.val + 1), by have := t.isLt; omega⟩

@[simp]
lemma middleStart_val (t : Fin (n - 2)) : (middleStart t).val = 3 * (t.val + 1) := rfl

lemma middleStart_injective : Function.Injective (middleStart (n := n)) := by
  intro a b equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp only [middleStart_val] at values
  omega

def middle : Finset (Fin (3 * n - 2)) := Finset.univ.image middleStart

@[simp]
lemma card_middle : (middle (n := n)).card = n - 2 := by
  rw [middle, Finset.card_image_of_injective _ middleStart_injective]
  simp

lemma intersect_subset_middle (p q : Rank n) (p_class : p.val % 3 = 0) (q_class : q.val % 3 = 2) :
    row p ∩ row q ⊆ middle := by
  intro j member
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.mem_inter.mp member).1
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finset.mem_inter.mp member).2
  have values := congrArg Fin.val (ha.trans hb.symm)
  simp only [start_val, p_class, q_class, Nat.add_zero] at values
  have positions : ¬a.val < p.val / 3 ∧ b.val < q.val / 3 ∧ a.val = b.val + 1 := by
    split_ifs at values <;> omega
  let t : Fin (n - 2) := ⟨b.val, by have := a.isLt; omega⟩
  apply Finset.mem_image.mpr
  refine ⟨t, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  have j_val := congrArg Fin.val ha
  simp only [start_val, p_class, Nat.add_zero, ite_eq_right positions.1] at j_val
  change 3 * (t.val + 1) = j.val
  dsimp [t]
  omega

lemma intersect_eq_middle (order : 2 ≤ n) {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (total : ∑ j, s j = (n : ℤ)) (p q : Rank n) (p_class : p.val % 3 = 0)
    (q_class : q.val % 3 = 2) (required_p : ∀ j ∈ row p, 1 ≤ s j)
    (required_q : ∀ j ∈ row q, 1 ≤ s j) : row p ∩ row q = middle := by
  apply Finset.eq_of_subset_of_card_le (intersect_subset_middle p q p_class q_class)
  rw [card_middle]
  exact (overlap_bound order positive total p q required_p required_q).2

lemma pillar_blocks_two (order : 2 ≤ n) (p q : Rank n) (p_class : p.val % 3 = 0)
    (q_class : q.val % 3 = 2) (overlap : row p ∩ row q = middle) :
    p.val / 3 ≤ 1 ∧ n - 2 ≤ q.val / 3 := by
  have p_bound := p.isLt
  have q_bound := q.isLt
  by_cases small : n ≤ 2
  · omega
  have first_common : middleStart (⟨0, by omega⟩ : Fin (n - 2)) ∈ row p ∩ row q := by
    rw [overlap]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have last_common : middleStart (⟨n - 3, by omega⟩ : Fin (n - 2)) ∈ row p ∩ row q := by
    rw [overlap]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.mem_inter.mp first_common).1
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finset.mem_inter.mp last_common).2
  have first_val := congrArg Fin.val ha
  have last_val := congrArg Fin.val hb
  simp only [start_val, middleStart_val, p_class, q_class, Nat.add_zero] at first_val last_val
  split_ifs at first_val last_val <;> omega

lemma pillar_positions_two (order : 2 ≤ n) {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (total : ∑ j, s j = (n : ℤ)) (p q : Rank n) (p_class : p.val % 3 = 0)
    (q_class : q.val % 3 = 2) (required_p : ∀ j ∈ row p, 1 ≤ s j)
    (required_q : ∀ j ∈ row q, 1 ≤ s j) :
    (p.val = 0 ∨ p.val = 3) ∧ (q.val = 3 * n - 4 ∨ q.val = 3 * n - 1) := by
  have overlap := intersect_eq_middle order positive total p q p_class q_class required_p required_q
  have blocks := pillar_blocks_two order p q p_class q_class overlap
  have p_bound := p.isLt
  have q_bound := q.isLt
  omega

lemma union_card_two (order : 2 ≤ n) (p q : Rank n) (overlap : row p ∩ row q = middle) :
    (row p ∪ row q).card = n := by
  have identity := Finset.card_union_add_card_inter (row p) (row q)
  rw [card_row, card_row, overlap, card_middle] at identity
  omega

lemma coefficients_two (order : 2 ≤ n) {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (total : ∑ j, s j = (n : ℤ)) (p q : Rank n) (p_class : p.val % 3 = 0)
    (q_class : q.val % 3 = 2) (required_p : ∀ j ∈ row p, 1 ≤ s j)
    (required_q : ∀ j ∈ row q, 1 ≤ s j) :
    s = fun j ↦ if j ∈ row p ∪ row q then 1 else 0 := by
  have overlap := intersect_eq_middle order positive total p q p_class q_class required_p required_q
  apply eq_indicator_of_sum_eq_card positive _
  · intro j member
    rcases Finset.mem_union.mp member with left | right
    · exact required_p j left
    · exact required_q j right
  · rw [union_card_two order p q overlap, total]

end Mahjong.VirtualHand.RequiredSequences
