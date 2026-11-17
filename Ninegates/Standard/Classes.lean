/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Graph
public import Ninegates.Wait.Classes

/-! The fixed classes of the eight standard families and the sharpness example
in the remarks after Propositions 5.9 and 5.10 of arXiv:2611.06944v1. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

variable {n : ℕ}

private lemma fixedClass_of_heavy {c : VirtualHand n} (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) (p q : Rank n) (heavy_p : 3 ≤ c p)
    (heavy_q : 3 ≤ c q) (s : ZMod 3) (sp : s ≠ rankClass p)
    (sq : s ≠ rankClass q) (pq : rankClass p ≠ rankClass q) : fixedClass c = s := by
  rcases three_classes_exhaust s (rankClass p) (rankClass q) sp sq pq
    (fixedClass c) with equal | equal | equal
  · exact equal
  · have bound := full.fixed_count_succ order p equal.symm
    omega
  · have bound := full.fixed_count_succ order q equal.symm
    omega

lemma fixedClass_B (order : 2 ≤ n) : fixedClass (B n) = 2 := by
  let p : Rank n := ⟨0, by omega⟩
  let q : Rank n := ⟨3 * n - 4, by omega⟩
  have class_p : rankClass p = 1 := rfl
  have class_q : rankClass q = 0 := by rw [rankClass_eq_zero_iff]; dsimp [q]; omega
  apply fixedClass_of_heavy order (B_full order) p q
  · rw [B_apply order]; dsimp [p]; norm_num
  · rw [B_apply order]; dsimp [q]; split_ifs <;> omega
  all_goals simp only [class_p, class_q]
  all_goals decide +kernel

lemma fixedClass_C (order : 2 ≤ n) : fixedClass (C n) = 1 := by
  let p : Rank n := ⟨2, by omega⟩
  let q : Rank n := ⟨3 * n - 2, by omega⟩
  have class_p : rankClass p = 0 := by rw [rankClass_eq_zero_iff]; rfl
  have class_q : rankClass q = 2 := by rw [rankClass_eq_two_iff]; dsimp [q]; omega
  apply fixedClass_of_heavy order (C_full order) p q
  · rw [C_apply order]; dsimp [p]; norm_num
  · rw [C_apply order]; dsimp [q]; split_ifs <;> omega
  all_goals simp only [class_p, class_q]
  all_goals decide +kernel

lemma fixedClass_D (order : 2 ≤ n) : fixedClass (D n) = 1 := by
  let p : Rank n := ⟨2, by omega⟩
  let q : Rank n := ⟨3 * n - 2, by omega⟩
  have class_p : rankClass p = 0 := by rw [rankClass_eq_zero_iff]; rfl
  have class_q : rankClass q = 2 := by rw [rankClass_eq_two_iff]; dsimp [q]; omega
  apply fixedClass_of_heavy order (D_full order) p q
  · rw [D_apply order]; norm_num [p]; split_ifs <;> omega
  · rw [D_apply order]; dsimp [q]; split_ifs <;> omega
  all_goals simp only [class_p, class_q]
  all_goals decide +kernel

lemma fixedClass_E (order : 2 ≤ n) : fixedClass (E n) = 2 := by
  let p : Rank n := ⟨3, by omega⟩
  let q : Rank n := ⟨3 * n - 4, by omega⟩
  have class_p : rankClass p = 1 := by rw [rankClass_eq_one_iff]; norm_num [p]
  have class_q : rankClass q = 0 := by rw [rankClass_eq_zero_iff]; dsimp [q]; omega
  apply fixedClass_of_heavy order (E_full order) p q
  · rw [E_apply order]; norm_num [p]; split_ifs <;> omega
  · rw [E_apply order]; dsimp [q]; split_ifs <;> omega
  all_goals simp only [class_p, class_q]
  all_goals decide +kernel

lemma fixedClass_B' (order : 2 ≤ n) : fixedClass (B' n) = 2 := by
  rw [B', (B_full order).fixedClass_reverse, fixedClass_B order]
  decide +kernel

lemma fixedClass_C' (order : 2 ≤ n) : fixedClass (C' n) = 0 := by
  rw [C', (C_full order).fixedClass_reverse, fixedClass_C order, sub_self]

lemma fixedClass_D' (order : 2 ≤ n) : fixedClass (D' n) = 0 := by
  rw [D', (D_full order).fixedClass_reverse, fixedClass_D order, sub_self]

/-- The fixed-class lower bound is attained by `A_n` at every positive order. -/
lemma A_classSizes (positive : 0 < n) :
    classSize 0 (A n) = (n : ℤ) + 2 ∧ classSize 1 (A n) = (n : ℤ) + 2 ∧
      classSize 2 (A n) = (n : ℤ) := by
  by_cases order : 2 ≤ n
  · have full := A_full order
    have fixed := fixedClass_A positive
    exact ⟨full.nonfixed_class_size_succ order 0 (by rw [fixed]; decide +kernel),
      full.nonfixed_class_size_succ order 1 (by rw [fixed]; decide +kernel),
      by simpa only [fixed] using full.fixed_class_size_succ order⟩
  · have one : n = 1 := by omega
    subst n
    decide +kernel

/-- The three equivalence classes listed in the remark after Proposition 5.10. -/
lemma fixedClass_partition (order : 2 ≤ n) {c : VirtualHand n} (family : EightFamily c) :
    (fixedClass c = 2 ↔ c = A n ∨ c = B n ∨ c = B' n ∨ c = E n) ∧
    (fixedClass c = 1 ↔ c = C n ∨ c = D n) ∧
    (fixedClass c = 0 ↔ c = C' n ∨ c = D' n) := by
  have different : (0 : ZMod 3) ≠ 1 ∧ (0 : ZMod 3) ≠ 2 ∧ (1 : ZMod 3) ≠ 2 := by
    decide +kernel
  have classes : fixedClass (A n) = 2 ∧ fixedClass (B n) = 2 ∧
      fixedClass (B' n) = 2 ∧ fixedClass (E n) = 2 ∧ fixedClass (C n) = 1 ∧
      fixedClass (D n) = 1 ∧ fixedClass (C' n) = 0 ∧ fixedClass (D' n) = 0 :=
    ⟨fixedClass_A (by omega), fixedClass_B order, fixedClass_B' order,
      fixedClass_E order, fixedClass_C order, fixedClass_D order,
      fixedClass_C' order, fixedClass_D' order⟩
  rcases family with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals grind

/-- `D_n` attains multiplicity two in its fixed class at paper rank four. -/
lemma D_fixed_bound_sharp (order : 2 ≤ n) :
    fixedClass (D n) = 1 ∧ ∃ i : Rank n, i.val = 3 ∧
      rankClass i = fixedClass (D n) ∧ D n i = 2 := by
  refine ⟨fixedClass_D order, ⟨3, by omega⟩, rfl, ?_, ?_⟩
  · rw [fixedClass_D order]
    rw [rankClass_eq_one_iff]
    norm_num
  · rw [D_apply order]
    norm_num
    omega

end Mahjong.VirtualHand.Standard
