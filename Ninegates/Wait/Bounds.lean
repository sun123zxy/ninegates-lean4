/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Positive
public import Ninegates.Wait.Classes
public import Ninegates.Hand.Interior
public import Ninegates.Hand.Neighbours

/-! Sharp lower bounds for the fixed and interchanging class sizes. The
nonnegative excess above one copy of each interior rank controls equality. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma IsFullWait.order_pos (h : IsFullWait m c) : 0 < n := by
  by_contra not_positive
  have zero : n = 0 := by omega
  subst n
  exact not_isFullWait_order_zero m c h

lemma IsFullWait.excess_nonnegative (h : IsFullWait m c) : Nonnegative (excess c) := by
  intro i
  change 0 ≤ c i - interiorOnes i
  by_cases interior : 0 < i.val ∧ i.val + 1 < 3 * n
  · rw [interiorOnes, ite_eq_left interior]
    exact sub_nonneg.mpr (h.interior_positive i interior.1 interior.2)
  · rw [interiorOnes, ite_eq_right interior, sub_zero]
    exact h.1 i

/-- The fixed-class part of `prp-class-size-lower-bounds`. -/
lemma IsFullWait.fixed_class_size (h : IsFullWait m c) :
    (n : ℤ) ≤ classSize (fixedClass c) c := by
  by_contra too_small
  have positive := h.excess_nonnegative
  have lower := classSize_interiorOnes_ge h.order_pos (fixedClass c)
  have remainder := positive.classSize_nonnegative (fixedClass c)
  have exhausted : classSize (fixedClass c) (excess c) = 0 := by
    rw [classSize_excess] at *
    omega
  have boundary : fixedClass c ≠ 2 := by
    intro equal
    rw [classSize_excess, equal, classSize_interiorOnes_two h.order_pos] at exhausted
    rw [equal] at too_small
    omega
  obtain ⟨i, class_i, base_i⟩ := exists_boundary_rank h.order_pos (fixedClass c) boundary
  have missing : c i = 0 := by
    have point := positive.le_classSize i
    rw [class_i, exhausted, excess_apply, base_i] at point
    have original : 0 ≤ c i := h.1 i
    omega
  obtain ⟨j, edge⟩ := (isFullWait_iff.mp h).2.2 i
  have class_j := edge.fixed_class_iff.mp class_i
  by_cases equal : i = j
  · subst j
    have available := edge.self_positive
    omega
  · have available := edge.pair_available equal
    have point := positive.le_classSize j
    rw [class_j, exhausted, excess_apply] at point
    have base := (interiorOnes_bounds j).2
    omega

/-- If a class of size at most `n` supplies a pair, it is a boundary class
with a unique interior rank of multiplicity two. -/
lemma IsFullWait.small_class_pair (h : IsFullWait m c) {r : ZMod 3}
    (small : classSize r c ≤ n) {q : Rank n} (class_q : rankClass q = r) (pair : 2 ≤ c q) :
    c q = 2 ∧ interiorOnes q = 1 ∧ r ≠ 2 ∧
      ∀ j : Rank n, rankClass j = r → j ≠ q → c j ≤ 1 := by
  have positive := h.excess_nonnegative
  have lower := classSize_interiorOnes_ge h.order_pos r
  have excess_size : classSize r (excess c) ≤ 1 := by rw [classSize_excess]; omega
  have point := positive.le_classSize q
  rw [class_q] at point
  have base := interiorOnes_bounds q
  have value : excess c q = 1 ∧ c q = 2 ∧ interiorOnes q = 1 := by
    rw [excess_apply] at *
    omega
  have boundary : r ≠ 2 := by
    intro equal
    rw [classSize_excess, equal, classSize_interiorOnes_two h.order_pos] at point
    rw [equal] at small
    omega
  refine ⟨value.2.1, value.2.2, boundary, ?_⟩
  intro j class_j different
  have combined := positive.add_le_classSize q j different.symm (class_j.trans class_q.symm)
  rw [class_q, value.1, excess_apply] at combined
  have base_j := (interiorOnes_bounds j).2
  omega

/-- The interchanging-class part of `prp-class-size-lower-bounds`. -/
lemma IsFullWait.nonfixed_class_size (h : IsFullWait m c) (r : ZMod 3)
    (nonfixed : r ≠ fixedClass c) : (n : ℤ) + 1 ≤ classSize r c := by
  by_contra too_small
  have small : classSize r c ≤ n := by omega
  have other : pairedClass c r ≠ r :=
    fun equal ↦ nonfixed ((pairedClass_eq_self_iff c r).mp equal)
  obtain ⟨i, class_i⟩ := exists_rankClass h.order_pos (pairedClass c r)
  obtain ⟨q, edge⟩ := (isFullWait_iff.mp h).2.2 i
  have class_q : rankClass q = r := by rw [edge.class_eq, class_i, pairedClass_pairedClass]
  have different : i ≠ q := by
    intro equal
    have same := congrArg rankClass equal
    rw [class_i, class_q] at same
    exact other same
  have available := edge.pair_available different
  obtain ⟨value, base, boundary, others⟩ := h.small_class_pair small class_q available
  have inside : 0 < q.val ∧ q.val + 1 < 3 * n := by
    by_contra outside
    have zero : interiorOnes q = 0 := by simp only [interiorOnes, ite_eq_right outside]
    omega
  have residue : q.val % 3 ≠ 1 := by
    intro equal
    exact boundary (class_q.symm.trans ((rankClass_eq_two_iff q).mpr equal))
  have room_left : 2 ≤ q.val := by omega
  have room_right : q.val + 2 < 3 * n := by omega
  have forced (a : Rank n) (class_a : rankClass a = pairedClass c r) : DrawPair c a q := by
    obtain ⟨j, hj⟩ := (isFullWait_iff.mp h).2.2 a
    have class_j : rankClass j = r := by rw [hj.class_eq, class_a, pairedClass_pairedClass]
    have a_ne : a ≠ j := by
      intro equal
      have same := congrArg rankClass equal
      rw [class_a, class_j] at same
      exact other same
    have available_j := hj.pair_available a_ne
    by_cases same : j = q
    · simpa only [same] using hj
    · have bound := others j class_j same
      omega
  obtain ⟨a, before, _, class_a⟩ := exists_class_before q room_left (pairedClass c r)
    (by rwa [class_q])
  obtain ⟨b, after, _, class_b⟩ := exists_class_after q room_right (pairedClass c r)
    (by rwa [class_q])
  have three := (forced a class_a).incoming_both_sides (forced b class_b) before after
  omega

/-- `prp-no-m-le-n-full-wait`, in the stronger implication form. -/
lemma IsFullWait.meldCount_gt_order (h : IsFullWait m c) : n < m := by
  have bound (r : ZMod 3) :
      (n : ℤ) + (if r = fixedClass c then 0 else 1) ≤ classSize r c := by
    by_cases equal : r = fixedClass c
    · simpa [equal] using h.fixed_class_size
    · simpa only [ite_eq_right equal] using h.nonfixed_class_size r equal
  have total := Finset.sum_le_sum (s := Finset.univ) (fun r _ ↦ bound r)
  have evaluate : (∑ r : ZMod 3, ((n : ℤ) + (if r = fixedClass c then 0 else 1))) =
      3 * (n : ℤ) + 2 := by
    calc
      _ = ∑ r : ZMod 3, (((n : ℤ) + 1) - (if r = fixedClass c then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro r _
        split_ifs <;> omega
      _ = _ := by simp [Finset.sum_sub_distrib]; ring
  rw [evaluate, ← size_eq_sum_classSize c, h.2.1] at total
  omega

end Mahjong.VirtualHand
