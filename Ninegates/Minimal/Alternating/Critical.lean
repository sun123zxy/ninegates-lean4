/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Scan
public import Ninegates.Minimal.Alternating.Full
public import Ninegates.Minimal.Alternating.Prefix

/-! Critical draws in the alternating part of the two constructions. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

def scanValue (b i q k : ℤ) : ℤ :=
  (baseSequence b k + SequenceImpulse.value i k + SequenceImpulse.value q k) % 3

lemma canonicalSequence_eq_value {n : ℕ} (order : 2 ≤ n) (i q : Rank n) (k : ℕ)
    (upper : k < 3 * n - 2) :
    canonicalSequence (hand n + single i - pair q) (k + 1) =
      scanValue ((n % 2 : ℕ) : ℤ) i.val q.val k :=
  canonicalSequence_formula order i q ⟨k, upper⟩

lemma canonicalTriplet_eq_value {n : ℕ} (order : 2 ≤ n) (i q k : Rank n)
    (lower : 2 ≤ k.val) (upper : k.val < 3 * n - 1) :
    canonicalTriplet (hand n + single i - pair q) k =
      ((hand n + single i - pair q) k -
        scanValue ((n % 2 : ℕ) : ℤ) i.val q.val (k.val - 1 : ℕ) -
        scanValue ((n % 2 : ℕ) : ℤ) i.val q.val (k.val - 2 : ℕ)) / 3 := by
  have first : k.val = (k.val - 1) + 1 := by omega
  have second : k.val - 1 = (k.val - 2) + 1 := by omega
  rw [canonicalTriplet_eq]
  rw [show canonicalSequence (hand n + single i - pair q) k.val = _ from
    by simpa only [← first] using canonicalSequence_eq_value order i q (k.val - 1) (by omega)]
  rw [show canonicalSequence (hand n + single i - pair q) (k.val - 1) = _ from
    by simpa only [← second] using canonicalSequence_eq_value order i q (k.val - 2) (by omega)]

private lemma scanValue_before {b i q k : ℤ} (positive : 0 ≤ b) (later : 2 + b ≤ k)
    (before : k < i) (after_pair : q ≤ k) :
    scanValue b i q k = (3 - (k - b) / 2 + Periodic.value 1 (-1) 0 (k - q)) % 3 := by
  rw [scanValue, baseSequence_of_ge positive later]
  simp only [SequenceImpulse.value, ite_eq_right (by omega : ¬i ≤ k),
    ite_eq_left after_pair, add_zero]

private lemma scanValue_at {b q k : ℤ} (positive : 0 ≤ b) (later : 2 + b ≤ k)
    (after_pair : q ≤ k) :
    scanValue b k q k = (3 - (k - b) / 2 + 1 + Periodic.value 1 (-1) 0 (k - q)) % 3 := by
  rw [scanValue, baseSequence_of_ge positive later]
  simp only [SequenceImpulse.value, le_refl, ite_true, sub_self,
    Periodic.value, Int.zero_emod, ite_eq_left after_pair]

lemma five_critical_values {b q k : ℤ} (positive : 0 ≤ b) (parity_bound : b ≤ 1)
    (pair_lower : 0 ≤ q) (pair_upper : q ≤ 2) (later : 4 + b ≤ k)
    (parity : (k + b) % 2 = 0) (congruent : (k + 3 + q + b) % 3 = 2) :
    scanValue b (k + 3) q (k - 1) = 2 ∧ scanValue b (k + 3) q (k - 2) = 1 := by
  rw [scanValue_before positive (by omega) (by omega) (by omega),
    scanValue_before positive (k := k - 2) (by omega) (by omega) (by omega)]
  unfold Periodic.value
  split_ifs <;> omega

lemma four_critical_values {b q k : ℤ} (positive : 0 ≤ b) (parity_bound : b ≤ 1)
    (pair_lower : 0 ≤ q) (pair_upper : q ≤ 2) (later : 4 + b ≤ k)
    (parity : (k + b) % 2 = 1) (congruent : (k - 1 + q + b) % 3 = 2) :
    scanValue b (k - 1) q (k - 1) = 0 ∧ scanValue b (k - 1) q (k - 2) = 2 := by
  rw [scanValue_at positive (by omega) (by omega),
    scanValue_before positive (k := k - 2) (by omega) (by omega) (by omega)]
  unfold Periodic.value
  split_ifs <;> omega

lemma four_sequence_values {b q k : ℤ} (positive : 0 ≤ b) (parity_bound : b ≤ 1)
    (pair_lower : 0 ≤ q) (pair_upper : q ≤ 2) (later : 4 + b ≤ k)
    (parity : (k + b) % 2 = 1) (congruent : (k + 2 + q + b) % 3 = 2) :
    scanValue b (k + 2) q k = 0 ∧ scanValue b (k + 2) q (k - 1) = 2 ∧
      scanValue b (k + 2) q (k - 2) = 2 := by
  rw [scanValue_before positive (by omega) (by omega) (by omega),
    scanValue_before positive (k := k - 1) (by omega) (by omega) (by omega),
    scanValue_before positive (k := k - 2) (by omega) (by omega) (by omega)]
  unfold Periodic.value
  split_ifs <;> omega

lemma hand_middle {n : ℕ} (k : Rank n) (later : 4 + n % 2 ≤ k.val)
    (upper : k.val < 3 * n - 2) :
    hand n k = if (k.val + n % 2) % 2 = 0 then 5 else 4 := by
  rw [hand_apply]
  have parity : (k.val + n) % 2 = (k.val + n % 2) % 2 := by omega
  rw [ite_eq_right (by omega : k.val ≠ 0), ite_eq_right (by omega : k.val ≠ 1),
    ite_eq_right (by omega : k.val ≠ 2), ite_eq_right (by omega : k.val ≠ 3),
    ite_eq_right (by omega : ¬3 * n - 2 ≤ k.val),
    ite_eq_right (by omega : ¬(n % 2 = 1 ∧ k.val = 4)), parity]

private lemma winning_middle {n : ℕ} (i q k : Rank n) (small : q.val < 3)
    (later : 4 ≤ k.val) (different : k.val ≠ i.val) :
    (hand n + single i - pair q) k = hand n k := by
  have not_i : k ≠ i := by intro equal; exact different (congrArg Fin.val equal)
  have not_q : k ≠ q := by intro equal; have := congrArg Fin.val equal; omega
  simp only [Pi.sub_apply, Pi.add_apply, single_of_ne not_i, pair_apply,
    single_of_ne not_q, mul_zero, add_zero, sub_zero]

lemma five_triplet_zero {n : ℕ} (order : 2 ≤ n) (i q k : Rank n)
    (later : 4 + n % 2 ≤ k.val) (upper : k.val < 3 * n - 2)
    (parity : (k.val + n % 2) % 2 = 0) (draw : i.val = k.val + 3)
    (edge : DrawPair (hand n) i q) :
    canonicalTriplet (hand n + single i - pair q) k = 0 := by
  have small := pair_lt_three order (i := i) (by omega) edge
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have values := five_critical_values (b := ((n % 2 : ℕ) : ℤ)) (q := q.val)
    (k := k.val) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have cast_one : ((k.val - 1 : ℕ) : ℤ) = (k.val : ℤ) - 1 := by omega
  have cast_two : ((k.val - 2 : ℕ) : ℤ) = (k.val : ℤ) - 2 := by omega
  have cast_draw : (i.val : ℤ) = (k.val : ℤ) + 3 := by omega
  rw [canonicalTriplet_eq_value order i q k (by omega) (by omega), cast_one, cast_two,
    cast_draw, values.1, values.2, winning_middle i q k small (by omega) (by omega),
    hand_middle k later upper, ite_eq_left parity]
  norm_num

lemma four_triplet_zero {n : ℕ} (order : 2 ≤ n) (i q k : Rank n)
    (later : 4 + n % 2 ≤ k.val) (upper : k.val < 3 * n - 2)
    (parity : (k.val + n % 2) % 2 = 1) (draw : i.val + 1 = k.val)
    (edge : DrawPair (hand n) i q) :
    canonicalTriplet (hand n + single i - pair q) k = 0 ∧
      canonicalSequence (hand n + single i - pair q) k.val = 0 := by
  have small := pair_lt_three order (i := i) (by omega) edge
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have values := four_critical_values (b := ((n % 2 : ℕ) : ℤ)) (q := q.val)
    (k := k.val) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have cast_one : ((k.val - 1 : ℕ) : ℤ) = (k.val : ℤ) - 1 := by omega
  have cast_two : ((k.val - 2 : ℕ) : ℤ) = (k.val : ℤ) - 2 := by omega
  have cast_draw : (i.val : ℤ) = (k.val : ℤ) - 1 := by omega
  constructor
  · rw [canonicalTriplet_eq_value order i q k (by omega) (by omega), cast_one, cast_two,
      cast_draw, values.1, values.2, winning_middle i q k small (by omega) (by omega),
      hand_middle k later upper, ite_eq_right (by omega : ¬(k.val + n % 2) % 2 = 0)]
    norm_num
  · have previous : k.val - 1 + 1 = k.val := by omega
    rw [← previous, canonicalSequence_eq_value order i q (k.val - 1) (by omega),
      cast_one, cast_draw, values.1]

lemma four_sequence_zero {n : ℕ} (order : 2 ≤ n) (i q k : Rank n)
    (later : 4 + n % 2 ≤ k.val) (upper : k.val < 3 * n - 2)
    (parity : (k.val + n % 2) % 2 = 1) (draw : i.val = k.val + 2)
    (edge : DrawPair (hand n) i q) :
    canonicalSequence (hand n + single i - pair q) (k.val + 1) = 0 ∧
      canonicalTriplet (hand n + single i - pair q) k = 0 := by
  have small := pair_lt_three order (i := i) (by omega) edge
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have values := four_sequence_values (b := ((n % 2 : ℕ) : ℤ)) (q := q.val)
    (k := k.val) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have cast_one : ((k.val - 1 : ℕ) : ℤ) = (k.val : ℤ) - 1 := by omega
  have cast_two : ((k.val - 2 : ℕ) : ℤ) = (k.val : ℤ) - 2 := by omega
  have cast_draw : (i.val : ℤ) = (k.val : ℤ) + 2 := by omega
  constructor
  · rw [canonicalSequence_eq_value order i q k.val upper, cast_draw, values.1]
  · rw [canonicalTriplet_eq_value order i q k (by omega) (by omega), cast_one, cast_two,
      cast_draw, values.2.1, values.2.2, winning_middle i q k small (by omega) (by omega),
      hand_middle k later upper, ite_eq_right (by omega : ¬(k.val + n % 2) % 2 = 0)]
    norm_num

end Mahjong.VirtualHand.AlternatingWait
