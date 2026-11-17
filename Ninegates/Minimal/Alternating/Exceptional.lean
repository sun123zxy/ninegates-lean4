/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Critical

/-! The two early critical draws whose pair may lie outside the first three ranks. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

private lemma even_triplet_values {q : ℤ} (lower : 2 ≤ q) :
    scanValue 0 3 q 0 = 2 ∧ scanValue 0 3 q 1 = 2 := by
  have zero : ¬q ≤ 0 := by omega
  have one : ¬q ≤ 1 := by omega
  norm_num [scanValue, baseSequence, SequenceImpulse.value, zero, one, Periodic.value]

lemma even_third_triplet_zero {n : ℕ} (order : 2 ≤ n) (even_order : n % 2 = 0)
    (i q : Rank n) (draw : i.val = 3) (edge : DrawPair (hand n) i q) :
    canonicalTriplet (hand n + single i - pair q) ⟨2, by omega⟩ = 0 := by
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have lower : 2 ≤ q.val := by omega
  have values := even_triplet_values (q := q.val) (by omega)
  rw [canonicalTriplet_eq_value order i q ⟨2, by omega⟩ (by norm_num) (by dsimp; omega)]
  norm_num only [Fin.val_mk, even_order, Nat.cast_zero, draw, Nat.cast_ofNat,
    Nat.reduceSub, values.1, values.2]
  simp only [Pi.sub_apply, Pi.add_apply, hand_apply, pair_apply, single_apply, Fin.ext_iff]
  norm_num [Fin.val_mk, draw]
  all_goals split_ifs <;> norm_num

private lemma even_sequence_values {q : ℤ} (lower : 3 ≤ q) :
    scanValue 0 2 q 1 = 2 ∧ scanValue 0 2 q 2 = 0 := by
  have one : ¬q ≤ 1 := by omega
  have two : ¬q ≤ 2 := by omega
  norm_num [scanValue, baseSequence, SequenceImpulse.value, one, two, Periodic.value]

lemma even_third_sequence_obstruction {n : ℕ} (order : 2 ≤ n) (even_order : n % 2 = 0)
    (i q : Rank n) (draw : i.val = 2) (edge : DrawPair (hand n) i q) :
    canonicalSequence (hand n + single i - pair q) 3 = 0 ∧
      canonicalTriplet (hand n + single i - pair q) ⟨3, by omega⟩ = 0 := by
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have residue : q.val % 3 = 0 := by omega
  by_cases small : q.val < 3
  · have pair_zero : q.val = 0 := by omega
    constructor
    · rw [canonicalSequence_eq_value order i q 2 (by omega)]
      norm_num [even_order, draw, pair_zero, scanValue, baseSequence,
        SequenceImpulse.value, Periodic.value]
    · rw [canonicalTriplet_eq_value order i q ⟨3, by omega⟩ (by norm_num) (by dsimp; omega)]
      norm_num [even_order, draw, pair_zero, scanValue, baseSequence,
        SequenceImpulse.value, Periodic.value, hand_apply, pair_apply, single_apply,
        Fin.ext_iff]
  · have values := even_sequence_values (q := q.val) (by omega)
    have previous : canonicalSequence (hand n + single i - pair q) 3 = 0 := by
      rw [canonicalSequence_eq_value order i q 2 (by omega)]
      simpa only [even_order, Nat.cast_zero, draw, Nat.cast_ofNat] using values.2
    have older : canonicalSequence (hand n + single i - pair q) 2 = 2 := by
      rw [canonicalSequence_eq_value order i q 1 (by omega)]
      simpa only [even_order, Nat.cast_zero, draw, Nat.cast_ofNat, Nat.cast_one] using values.1
    refine ⟨previous, ?_⟩
    have nonnegative := edge.canonicalTriplet_nonnegative (⟨3, by omega⟩ : Rank n)
    have pair_nonnegative : (0 : ℤ) ≤ pair q (⟨3, by omega⟩ : Rank n) :=
      nonnegative_pair q _
    rw [canonicalTriplet_eq]
    change ((hand n + single i - pair q) ⟨3, by omega⟩ -
      canonicalSequence _ 3 - canonicalSequence _ 2) / 3 = 0
    rw [previous, older]
    have at_three : (hand n + single i - pair q) ⟨3, by omega⟩ ≤ 3 := by
      have base : hand n (⟨3, by omega⟩ : Rank n) = 3 := rfl
      have no_draw : single i (⟨3, by omega⟩ : Rank n) = 0 := by
        simp [Fin.ext_iff, draw]
      change hand n _ + single i _ - pair q _ ≤ 3
      rw [base, no_draw]
      linarith
    rw [canonicalTriplet_eq] at nonnegative
    change 0 ≤ ((hand n + single i - pair q) ⟨3, by omega⟩ -
      canonicalSequence _ 3 - canonicalSequence _ 2) / 3 at nonnegative
    rw [previous, older] at nonnegative
    omega

end Mahjong.VirtualHand.AlternatingWait
