/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Double.Full
public import Ninegates.Meldable.Placement

/-! Two constraints on winning placements of the double-tile family. The
first draw must self-pair; a middle draw forbids the sequence just before it. -/

@[expose] public section

namespace Mahjong.VirtualHand.DoubleWait

variable {n : ℕ}

private def model (first : Rank n) (a : ℤ) : Placement n :=
  ⟨fun r ↦ Periodic.value a (2 - a) 0 r.val, single first⟩

private lemma model_canonic (first : Rank n) (a : ℤ) (lower : 0 ≤ a) (upper : a ≤ 1) :
    (model first a).Canonic := by
  intro r
  dsimp only [model]
  unfold Periodic.value
  split_ifs <;> omega

private lemma model_prefix (first : Rank n) (zero : first.val = 0) (a : ℤ) (i : Rank n)
    (upper : i.val < 3 * n - 2) : (model first a).toHand i = hand n i + a * single first i := by
  rw [Placement.toHand_eq]
  simp only [model, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Periodic.sequenceHand_prefix a (2 - a) 0 i upper]
  simp only [hand_apply, single_apply, Fin.ext_iff, zero]
  split_ifs <;> ring

private lemma scan_of_prefix (first : Rank n) (zero : first.val = 0) (a : ℤ)
    (lower : 0 ≤ a) (upper : a ≤ 1) {d : VirtualHand n} (cut : ℕ) (bound : cut ≤ 3 * n - 2)
    (prefix_eq : ∀ i, i.val < cut → d i = hand n i + a * single first i)
    (j : ℕ) (positive : 1 ≤ j) (inside : j ≤ cut) :
    canonicalSequence d j = Periodic.value a (2 - a) 0 ((j : ℤ) - 1) := by
  have canonical := model_canonic first a lower upper
  have same := (canonicalSequence_prefix_iff d (model first a).toHand cut (by omega)).mp
    (fun i before ↦ congrArg (fun z : ℤ ↦ (z : ZMod 3))
      ((prefix_eq i before).trans (model_prefix first zero a i (by omega)).symm))
  rw [same j inside, canonical.canonicalSequence_eq j (by omega)]
  change coefficient (fun r : Fin (3 * n - 2) ↦ Periodic.value a (2 - a) 0 r.val)
    ((j : ℤ) - 1) = _
  rw [Periodic.coefficient_value, ite_eq_left (by omega)]

lemma first_draw_pair {first q : Rank n} (zero : first.val = 0)
    (edge : DrawPair (hand n) first q) : q = first := by
  have positive : 0 < n := by have := first.isLt; omega
  have class_first : rankClass first = 1 := by rw [rankClass_eq_one_iff, zero]
  have class_q : rankClass q = 1 := by
    have fixed_first : rankClass first = fixedClass (hand n) :=
      class_first.trans (fixedClass_hand positive).symm
    simpa only [fixedClass_hand positive] using edge.fixed_class_iff.mp fixed_first
  have residue := (rankClass_eq_one_iff q).mp class_q
  by_contra different
  have lower : 3 ≤ q.val := by
    have nonzero : q.val ≠ 0 := by intro equal; exact different (Fin.ext (equal.trans zero.symm))
    omega
  have bound := q.isLt
  let d := hand n + single first - pair q
  have prefix_eq : ∀ i : Rank n, i.val < q.val → d i = hand n i + 1 * single first i := by
    intro i before
    have different_i : i ≠ q := by intro same; subst i; omega
    simp only [d, Pi.sub_apply, Pi.add_apply, pair_apply, single_of_ne different_i,
      mul_zero, sub_zero, one_mul]
  have previous : canonicalSequence d q.val = 0 := by
    rw [scan_of_prefix first zero 1 (by norm_num) (by norm_num) q.val (by omega)
      prefix_eq q.val (by omega) le_rfl]
    unfold Periodic.value
    split_ifs <;> omega
  have older : canonicalSequence d (q.val - 1) = 1 := by
    rw [scan_of_prefix first zero 1 (by norm_num) (by norm_num) q.val (by omega)
      prefix_eq (q.val - 1) (by omega) (by omega)]
    unfold Periodic.value
    split_ifs <;> omega
  have at_q : d q = 0 := by
    simp only [d, Pi.sub_apply, Pi.add_apply, hand_apply, pair_apply, single_self,
      single_of_ne different]
    rw [ite_eq_right (by omega)]
    norm_num
  have actual : 0 ≤ canonicalTriplet d q := edge.canonicalTriplet_nonnegative q
  rw [canonicalTriplet_eq, at_q, previous, older] at actual
  norm_num at actual

lemma middle_pair_right {i q : Rank n} (middle : i.val % 3 = 1)
    (edge : DrawPair (hand n) i q) : i.val < q.val := by
  have positive : 0 < n := by have := i.isLt; omega
  let first : Rank n := ⟨0, by omega⟩
  have class_i : rankClass i = 2 := (rankClass_eq_two_iff i).mpr middle
  have class_q : rankClass q = 0 := by
    rw [edge.class_eq, class_i, pairedClass, fixedClass_hand positive]
    decide +kernel
  have residue := (rankClass_eq_zero_iff q).mp class_q
  by_contra not_after
  have lower : 2 ≤ q.val := by omega
  have before : q.val < i.val := by omega
  have bound := i.isLt
  let d := hand n + single i - pair q
  have prefix_eq : ∀ k : Rank n, k.val < q.val → d k = hand n k + 0 * single first k := by
    intro k prior
    have different_i : k ≠ i := by intro same; subst k; omega
    have different_q : k ≠ q := by intro same; subst k; omega
    simp only [d, Pi.sub_apply, Pi.add_apply, pair_apply, single_of_ne different_i,
      single_of_ne different_q, mul_zero, add_zero, sub_zero, zero_mul]
  have previous : canonicalSequence d q.val = 2 := by
    rw [scan_of_prefix first rfl 0 (by norm_num) (by norm_num) q.val (by omega)
      prefix_eq q.val (by omega) le_rfl]
    unfold Periodic.value
    split_ifs <;> omega
  have older : canonicalSequence d (q.val - 1) = 0 := by
    rw [scan_of_prefix first rfl 0 (by norm_num) (by norm_num) q.val (by omega)
      prefix_eq (q.val - 1) (by omega) (by omega)]
    unfold Periodic.value
    split_ifs <;> omega
  have different : q ≠ i := by intro same; subst q; omega
  have at_q : d q = 0 := by
    simp only [d, Pi.sub_apply, Pi.add_apply, hand_apply, pair_apply, single_self,
      single_of_ne different]
    rw [ite_eq_right (by omega)]
    norm_num
  have actual : 0 ≤ canonicalTriplet d q := edge.canonicalTriplet_nonnegative q
  rw [canonicalTriplet_eq, at_q, previous, older] at actual
  norm_num at actual

lemma middle_draw_no_block (r : Fin (3 * n - 2)) (block : r.val % 3 = 0)
    {i q : Rank n} (next : i.val = r.val + 1) (edge : DrawPair (hand n) i q)
    {p : Placement n} (actual : p.Nonnegative) (equal : p.toHand = hand n + single i - pair q) :
    p.seqNum r = 0 := by
  have positive : 0 < n := by have := i.isLt; omega
  let first : Rank n := ⟨0, by omega⟩
  have middle : i.val % 3 = 1 := by omega
  have after := middle_pair_right middle edge
  have bound := i.isLt
  let d := hand n + single i - pair q
  have prefix_eq : ∀ k : Rank n, k.val < i.val → d k = hand n k + 0 * single first k := by
    intro k prior
    have different_i : k ≠ i := by intro same; subst k; omega
    have different_q : k ≠ q := by intro same; subst k; omega
    simp only [d, Pi.sub_apply, Pi.add_apply, pair_apply, single_of_ne different_i,
      single_of_ne different_q, mul_zero, add_zero, sub_zero, zero_mul]
  have zero_sequence : canonicalSequence d (r.val + 1) = 0 := by
    rw [scan_of_prefix first rfl 0 (by norm_num) (by norm_num) i.val (by omega)
      prefix_eq (r.val + 1) (by omega) (by omega)]
    unfold Periodic.value
    split_ifs <;> omega
  have residue := p.seqNum_emod_eq_canonicalSequence r
  rw [equal] at residue
  rw [show canonicalSequence (hand n + single i - pair q) (r.val + 1) = 0 from zero_sequence]
    at residue
  let last : Rank n := ⟨r.val + 2, by omega⟩
  have bound_sequence := actual.seqNum_le_last r
  have bound_hand : p.toHand last ≤ 2 := by
    rw [equal]
    have different_i : last ≠ i := by
      intro same
      have := congrArg Fin.val same
      dsimp [last] at *
      omega
    have pair_positive : 0 ≤ pair q last := nonnegative_pair q last
    simp only [Pi.sub_apply, Pi.add_apply, hand_apply, single_of_ne different_i]
    rw [ite_eq_right (by dsimp [last]; omega)]
    linarith
  have bound_two : p.seqNum r ≤ 2 := le_trans bound_sequence bound_hand
  have lower : 0 ≤ p.seqNum r := actual.1 r
  omega

end Mahjong.VirtualHand.DoubleWait
