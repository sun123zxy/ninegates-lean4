/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Required
public import Ninegates.Meldable.RequiredOne

/-! The fixed-class-one case: an extra sequence at start zero or one forces
the two required rows to coincide, leaving precisely the two paper templates. -/

@[expose] public section

namespace Mahjong.VirtualHand.Pillars

variable {n : ℕ} {c : VirtualHand n} {p q : Rank n}

private lemma low_q_extra (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) (fixed : fixedClass c = 1) (class_p : rankClass p = 0)
    (class_q : rankClass q = 2) (low : q.val = 1) {s : Fin (3 * n - 2) → ℤ}
    (equal : sequenceHand s = c - pair p - pair q) : 1 ≤ s ⟨0, by omega⟩ := by
  let first : Rank n := ⟨0, by omega⟩
  let zero : Fin (3 * n - 2) := ⟨0, by omega⟩
  have nonfixed_q := pillars.nonfixed_q
  have total : classSize 2 (excess c) = 2 := by
    rw [classSize_excess, ← class_q, full.nonfixed_class_size_succ order _ nonfixed_q,
      class_q, classSize_interiorOnes_two full.order_pos]
    omega
  have point := full.excess_nonnegative.le_classSize q
  rw [class_q, total, excess_apply] at point
  have base := (interiorOnes_bounds q).2
  have count_q : c q = 3 := by have lower := pillars.pillar_q.1; omega
  have first_class : rankClass first = 1 := rfl
  have first_p : first ≠ p := by
    intro same
    have classes := congrArg rankClass same
    rw [first_class, class_p] at classes
    norm_num at classes
  have first_q : first ≠ q := by
    intro same
    have values := congrArg Fin.val same
    dsimp [first] at values
    omega
  have count_first : 1 ≤ c first := by
    by_contra small
    have nonnegative : 0 ≤ c first := full.1 first
    have missing_first : c first = 0 := by omega
    obtain ⟨j, edge⟩ := (isFullWait_iff.mp full).2.2 first
    have fixed_first : rankClass first = fixedClass c := first_class.trans fixed.symm
    have fixed_j := edge.fixed_class_iff.mp fixed_first
    have first_j : first ≠ j := by
      intro same
      subst j
      have available := edge.self_positive
      omega
    have q_j : q ≠ j := by
      intro same
      have classes := (congrArg rankClass same).trans fixed_j
      rw [class_q, fixed] at classes
      have different : (2 : ZMod 3) ≠ 1 := by decide +kernel
      exact different classes
    let remainder := c + single first - pair j - triplet p - triplet q
    have actual : Meldable remainder :=
      (pillars.fixed_draw_sequential_succ order full edge fixed_first).meldable
    have missing_q : remainder q = 0 := by
      simp only [remainder, Pi.sub_apply, Pi.add_apply, single_of_ne first_q.symm,
        pair_apply, single_of_ne q_j, triplet_apply, single_of_ne pillars.different.symm,
        single_self, count_q]
      norm_num
    have at_first : remainder first = 1 := by
      simp only [remainder, Pi.sub_apply, Pi.add_apply, single_self, pair_apply,
        single_of_ne first_j, triplet_apply, single_of_ne first_p, single_of_ne first_q,
        missing_first]
      norm_num
    have cut : leftOf q remainder = single first := by
      ext i
      by_cases at_zero : i.val = 0
      · have same : i = first := Fin.ext at_zero
        subst i
        simp only [leftOf_apply, low, first, at_first, single_self]
        norm_num
      · have late : ¬i.val < q.val := by omega
        have different : i ≠ first := by
          intro same
          have values := congrArg Fin.val same
          exact at_zero values
        simp only [leftOf_apply, ite_eq_right late, single_of_ne different]
    have left := actual.leftOf q missing_q
    rw [cut] at left
    have count := left.virtuallyMeldable.size_cast
    simp at count
  have at_first := congrFun equal first
  simp only [sequenceHand_apply, first] at at_first
  rw [coefficient_fin s zero, coefficient_of_neg s (by norm_num),
    coefficient_of_neg s (by norm_num)] at at_first
  have rest : (c - pair p - pair q) first = c first := by
    simp only [Pi.sub_apply, pair_apply, single_of_ne first_p, single_of_ne first_q,
      mul_zero, sub_zero]
  rw [rest] at at_first
  change 1 ≤ s zero
  omega

lemma fixed_one_decomposition_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) (fixed : fixedClass c = 1) (class_p : rankClass p = 0) :
    p.val = 2 ∧ q.val = 3 * n - 2 ∧
      ∃ k : Fin (3 * n - 2), k.val ≤ 1 ∧ c = pair p + pair q + sequenceHand
        (fun j ↦ if j ∈ insert k RequiredSequences.third then 1 else 0) := by
  have class_q : rankClass q = 2 := by
    rw [pillars.class_q, pairedClass, fixed, class_p]
    decide +kernel
  have p_class := (rankClass_eq_zero_iff p).mp class_p
  have q_class := (rankClass_eq_two_iff q).mp class_q
  obtain ⟨s, positive, equal, total, required_p, required_q⟩ :=
    pillars.exists_sequence_rows_succ order full
  let zero : Fin (3 * n - 2) := ⟨0, by omega⟩
  let one : Fin (3 * n - 2) := ⟨1, by omega⟩
  have outside_zero : zero ∉ RequiredSequences.row p ∪ RequiredSequences.row q := by
    intro member
    rcases Finset.mem_union.mp member with left | right
    · have lower := RequiredSequences.row_ge_remainder left
      dsimp [zero] at lower
      omega
    · have lower := RequiredSequences.row_ge_remainder right
      dsimp [zero] at lower
      omega
  obtain ⟨k, low, outside, extra⟩ : ∃ k : Fin (3 * n - 2), k.val ≤ 1 ∧
      k ∉ RequiredSequences.row p ∪ RequiredSequences.row q ∧ 1 ≤ s k := by
    by_cases low_q : q.val = 1
    · exact ⟨zero, by dsimp [zero]; omega, outside_zero,
        low_q_extra pillars order full fixed class_p class_q low_q equal⟩
    · let second : Rank n := ⟨1, by omega⟩
      have q_later : 0 < q.val / 3 := by omega
      have second_q : second ≠ q := by
        intro same
        have values := congrArg Fin.val same
        dsimp [second] at values
        omega
      have second_p : second ≠ p := by
        intro same
        have values := congrArg Fin.val same
        dsimp [second] at values
        omega
      have original : c second = 1 := by
        have lower := full.interior_positive second (by dsimp [second]; omega)
          (by dsimp [second]; omega)
        by_contra different
        have pair : 2 ≤ c second := by omega
        have same_class : rankClass second = rankClass q := by
          rw [class_q, rankClass_eq_two_iff]
          norm_num [second]
        have same := pillars.pillar_q.2 second same_class pair
        exact second_q same
      have at_second := congrFun equal second
      have current : (second.val : ℤ) = one.val := rfl
      have previous : (second.val : ℤ) - 1 = zero.val := by dsimp [second, zero]
      have older : (second.val : ℤ) - 2 < 0 := by dsimp [second]; norm_num
      rw [sequenceHand_apply, current, coefficient_fin s one] at at_second
      rw [previous, coefficient_fin s zero, coefficient_of_neg s older] at at_second
      have rest : (c - pair p - pair q) second = 1 := by
        simp only [Pi.sub_apply, pair_apply, single_of_ne second_p, single_of_ne second_q,
          mul_zero, sub_zero, original]
      rw [rest] at at_second
      have outside_one : one ∉ RequiredSequences.row p ∪ RequiredSequences.row q := by
        intro member
        rcases Finset.mem_union.mp member with left | right
        · have lower := RequiredSequences.row_ge_remainder left
          dsimp [one] at lower
          omega
        · exact RequiredSequences.one_not_mem_row q q_class q_later one rfl right
      by_cases zero_extra : 1 ≤ s zero
      · exact ⟨zero, by dsimp [zero]; omega, outside_zero, zero_extra⟩
      · refine ⟨one, by dsimp [one]; omega, outside_one, ?_⟩
        omega
  have shape := RequiredSequences.coefficients_one order positive total p q p_class q_class
    required_p required_q k outside extra
  refine ⟨shape.1, shape.2.1, k, low, ?_⟩
  rw [← shape.2.2, equal]
  abel

end Mahjong.VirtualHand.Pillars
