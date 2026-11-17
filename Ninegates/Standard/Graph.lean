/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Classification
public import Ninegates.Standard.One

/-! The exact draw-pair graph of Nine Gates, including order one
(arXiv:2611.06944v1, Example 4.5). -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

lemma A_full_positive {n : ℕ} (positive : 0 < n) : IsFullWait (n + 1) (A n) := by
  by_cases order : 2 ≤ n
  · exact A_full order
  · have one : n = 1 := by omega
    subst n
    have equal : A 1 = One 0 := by decide +kernel
    rw [equal]
    exact (One_live 0).1

lemma fixedClass_A {n : ℕ} (positive : 0 < n) : fixedClass (A n) = 2 := by
  have three : (3 : ZMod 3) = 0 := by decide +kernel
  have zero : (3 : ZMod 3) * (n : ZMod 3) = 0 := by rw [three, zero_mul]
  unfold fixedClass
  rw [A, map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat, three,
    zero_mul, add_zero]
  rw [rankSum_cast_eq_classSizes,
    classSize_interiorOnes_nonTwo positive 1 (by decide +kernel),
    classSize_interiorOnes_two positive]
  push_cast
  linear_combination zero - three

private lemma A_drawPair_necessary {n : ℕ} (positive : 0 < n) {i j : Rank n}
    (edge : DrawPair (A n) i j) :
    (rankClass i = 0 ∧ j.val = 0) ∨
      (rankClass i = 1 ∧ j.val + 1 = 3 * n) ∨ (rankClass i = 2 ∧ j = i) := by
  have three : (3 : ZMod 3) = 0 := by decide +kernel
  have congruent := edge.congruence
  change rankClass i + rankClass j = -fixedClass (A n) at congruent
  rw [fixedClass_A positive] at congruent
  by_cases same : i = j
  · subst j
    have fixed := edge.self_fixed_class
    rw [fixedClass_A positive] at fixed
    exact Or.inr (Or.inr ⟨fixed, rfl⟩)
  · have copies := edge.pair_available same
    rw [A_apply] at copies
    have boundary : j.val = 0 ∨ j.val + 1 = 3 * n := by split_ifs at copies <;> omega
    rcases boundary with first | last
    · have class_j : rankClass j = 1 := by rw [rankClass_eq_one_iff]; omega
      rw [class_j] at congruent
      exact Or.inl ⟨by linear_combination congruent - three, first⟩
    · have class_j : rankClass j = 0 := by rw [rankClass_eq_zero_iff]; omega
      rw [class_j] at congruent
      exact Or.inr (Or.inl ⟨by linear_combination congruent - three, last⟩)

lemma A_drawPair_iff {n : ℕ} (positive : 0 < n) (i j : Rank n) :
    DrawPair (A n) i j ↔ (rankClass i = 0 ∧ j.val = 0) ∨
      (rankClass i = 1 ∧ j.val + 1 = 3 * n) ∨ (rankClass i = 2 ∧ j = i) := by
  refine ⟨A_drawPair_necessary positive, ?_⟩
  intro target
  obtain ⟨q, edge⟩ := (isFullWait_iff.mp (A_full_positive positive)).2.2 i
  have allowed := A_drawPair_necessary positive edge
  have zero_one : (0 : ZMod 3) ≠ 1 := by decide +kernel
  have zero_two : (0 : ZMod 3) ≠ 2 := by decide +kernel
  have one_two : (1 : ZMod 3) ≠ 2 := by decide +kernel
  have equal : q = j := by
    apply Fin.ext
    rcases allowed with ⟨class_q, at_q⟩ | ⟨class_q, at_q⟩ | ⟨class_q, at_q⟩
    all_goals
      rcases target with ⟨class_j, at_j⟩ | ⟨class_j, at_j⟩ | ⟨class_j, at_j⟩
      all_goals simp_all [Fin.ext_iff]
      all_goals omega
  simpa only [equal] using edge

end Mahjong.VirtualHand.Standard
