/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.SequentialMoving
public import Ninegates.Meldable.Statistics

/-! The row of `n-1` distinct sequence starts forced by moving a tile to both
ends of its class. Finite-sum bounds control the overlap of two such rows. -/

@[expose] public section

namespace Mahjong.VirtualHand.RequiredSequences

variable {n : ℕ}

def first (i : Rank n) : Rank n := ⟨i.val % 3, by have := i.isLt; omega⟩
def last (i : Rank n) : Rank n := ⟨3 * (n - 1) + i.val % 3, by have := i.isLt; omega⟩

@[simp]
lemma first_val (i : Rank n) : (first i).val = i.val % 3 := rfl

@[simp]
lemma last_val (i : Rank n) : (last i).val = 3 * (n - 1) + i.val % 3 := rfl

lemma first_le (i : Rank n) : (first i).val ≤ i.val := by simp; omega
lemma le_last (i : Rank n) : i.val ≤ (last i).val := by have := i.isLt; simp; omega

lemma first_class (i : Rank n) : rankClass (first i) = rankClass i := by
  rw [rankClass_eq_iff]
  simp

lemma last_class (i : Rank n) : rankClass (last i) = rankClass i := by
  rw [rankClass_eq_iff]
  simp

/-- One start for each gap between consecutive ranks of the source's class. -/
def start (i : Rank n) (t : Fin (n - 1)) : Fin (3 * n - 2) :=
  ⟨3 * t.val + i.val % 3 + (if t.val < i.val / 3 then 1 else 0), by
    have := i.isLt
    have := t.isLt
    split_ifs <;> omega⟩

@[grind =]
lemma start_val (i : Rank n) (t : Fin (n - 1)) :
    (start i t).val = 3 * t.val + i.val % 3 + (if t.val < i.val / 3 then 1 else 0) := rfl

lemma start_injective (i : Rank n) : Function.Injective (start i) := by
  intro a b equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp only [start_val] at values
  split_ifs at values <;> omega

def row (i : Rank n) : Finset (Fin (3 * n - 2)) := Finset.univ.image (start i)

@[simp]
lemma card_row (i : Rank n) : (row i).card = n - 1 := by
  rw [row, Finset.card_image_of_injective _ (start_injective i)]
  simp

lemma row_ge_remainder {i : Rank n} {j : Fin (3 * n - 2)} (member : j ∈ row i) :
    i.val % 3 ≤ j.val := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp member
  simp only [start_val]
  split_ifs <;> omega

lemma start_required {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s) (i : Rank n)
    (left : Sequential (moveTile (sequenceHand s) i (first i)))
    (right : Sequential (moveTile (sequenceHand s) i (last i))) (t : Fin (n - 1)) :
    1 ≤ s (start i t) := by
  have left_required := ((sequential_moveTile_left_iff positive i (first i) (first_le i)).mp left).2
  have right_required :=
    ((sequential_moveTile_right_iff positive i (last i) (le_last i)).mp right).2
  have bound_i := i.isLt
  have bound_t := t.isLt
  by_cases before : t.val < i.val / 3
  · apply left_required (start i t)
    all_goals simp only [start_val, first_val, ite_eq_left before]; omega
  · apply right_required (start i t)
    all_goals simp only [start_val, last_val, ite_eq_right before]; omega

lemma row_required {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s) (i : Rank n)
    (moves : ∀ j : Rank n, rankClass j = rankClass i →
      Sequential (moveTile (sequenceHand s) i j)) :
    ∀ j ∈ row i, 1 ≤ s j := by
  intro j member
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp member
  exact start_required positive i (moves (first i) (first_class i))
    (moves (last i) (last_class i)) t

section Counting

variable {α : Type*} [Fintype α]

lemma card_le_sum {s : α → ℤ} (positive : 0 ≤ s) (r : Finset α)
    (required : ∀ j ∈ r, 1 ≤ s j) : (r.card : ℤ) ≤ ∑ j, s j := by
  calc
    _ = ∑ j ∈ r, (1 : ℤ) := by simp
    _ ≤ ∑ j ∈ r, s j := Finset.sum_le_sum required
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ r) (fun j _ _ ↦ positive j)

lemma eq_indicator_of_sum_eq_card [DecidableEq α] {s : α → ℤ} (positive : 0 ≤ s) (r : Finset α)
    (required : ∀ j ∈ r, 1 ≤ s j) (total : ∑ j, s j = (r.card : ℤ)) :
    s = fun j ↦ if j ∈ r then 1 else 0 := by
  have nonnegative (j : α) : 0 ≤ s j - (if j ∈ r then 1 else 0) := by
    split_ifs with member
    · exact sub_nonneg.mpr (required j member)
    · simpa using positive j
  have difference : (∑ j, (s j - (if j ∈ r then 1 else 0))) = 0 := by
    simp [Finset.sum_sub_distrib, total]
  ext j
  have bound := Finset.single_le_sum (fun k _ ↦ nonnegative k) (Finset.mem_univ j)
  rw [difference] at bound
  have nonnegative_j := nonnegative j
  omega

lemma card_add_one_le_sum {s : α → ℤ} (positive : 0 ≤ s) (r : Finset α)
    (required : ∀ j ∈ r, 1 ≤ s j) (k : α) (outside : k ∉ r) (extra : 1 ≤ s k) :
    (r.card : ℤ) + 1 ≤ ∑ j, s j := by
  classical
  have bound := card_le_sum positive (insert k r) (by
    intro j member
    rcases Finset.mem_insert.mp member with same | inside
    · simpa only [same] using extra
    · exact required j inside)
  simpa [Finset.card_insert_of_notMem outside] using bound

end Counting

lemma overlap_bound (order : 2 ≤ n) {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (total : ∑ j, s j = (n : ℤ)) (p q : Rank n)
    (required_p : ∀ j ∈ row p, 1 ≤ s j) (required_q : ∀ j ∈ row q, 1 ≤ s j) :
    (row p ∪ row q).card ≤ n ∧ n - 2 ≤ (row p ∩ row q).card := by
  have union := card_le_sum positive (row p ∪ row q) (by
    intro j member
    rcases Finset.mem_union.mp member with left | right
    · exact required_p j left
    · exact required_q j right)
  rw [total] at union
  have identity := Finset.card_union_add_card_inter (row p) (row q)
  rw [card_row, card_row] at identity
  omega

lemma rows_equal_of_extra (order : 2 ≤ n) {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (total : ∑ j, s j = (n : ℤ)) (p q : Rank n)
    (required_p : ∀ j ∈ row p, 1 ≤ s j) (required_q : ∀ j ∈ row q, 1 ≤ s j)
    (k : Fin (3 * n - 2)) (outside : k ∉ row p ∪ row q) (extra : 1 ≤ s k) : row p = row q := by
  have bound := card_add_one_le_sum positive (row p ∪ row q) (by
    intro j member
    rcases Finset.mem_union.mp member with left | right
    · exact required_p j left
    · exact required_q j right) k outside extra
  rw [total] at bound
  have left : row p = row p ∪ row q := by
    apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
    rw [card_row]
    omega
  have right : row q = row p ∪ row q := by
    apply Finset.eq_of_subset_of_card_le Finset.subset_union_right
    rw [card_row]
    omega
  exact left.trans right.symm

end Mahjong.VirtualHand.RequiredSequences
