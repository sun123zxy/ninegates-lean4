/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Defs
public import Ninegates.Meldable.Impulse
public import Ninegates.Meldable.Scan

/-! A closed formula for every legal canonical sequence coefficient after
a draw and a pair removal. It separates the base hand and the two impulses. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

def baseSequence (b k : ℤ) : ℤ :=
  if k < 0 then 0 else if k < 2 + b then 2 else 3 - (k - b) / 2

def sequenceCoefficients {n : ℕ} (i q : Rank n) (r : Fin (3 * n - 2)) : ℤ :=
  (baseSequence ((n % 2 : ℕ) : ℤ) r.val + SequenceImpulse.value i.val r.val +
    SequenceImpulse.value q.val r.val) % 3

lemma baseSequence_of_ge {b k : ℤ} (positive : 0 ≤ b) (bound : 2 + b ≤ k) :
    baseSequence b k = 3 - (k - b) / 2 := by
  unfold baseSequence
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private lemma base_convolution_tail {b k : ℤ} (positive : 0 ≤ b) (upper : b ≤ 1)
    (later : 5 ≤ k) :
    (baseSequence b k + baseSequence b (k - 1) + baseSequence b (k - 2)) % 3 =
      if (k + b) % 2 = 0 then 2 else 1 := by
  rw [baseSequence_of_ge positive (by omega), baseSequence_of_ge positive (k := k - 1) (by omega),
    baseSequence_of_ge positive (k := k - 2) (by omega)]
  have b_cases : b = 0 ∨ b = 1 := by omega
  have k_cases : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases b_cases with at_b | at_b <;> rcases k_cases with at_k | at_k
  all_goals split_ifs <;> omega

private lemma base_congruence {n : ℕ} (order : 2 ≤ n) (r : Fin (3 * n - 2)) :
    (baseSequence ((n % 2 : ℕ) : ℤ) r.val +
      baseSequence ((n % 2 : ℕ) : ℤ) ((r.val : ℤ) - 1) +
        baseSequence ((n % 2 : ℕ) : ℤ) ((r.val : ℤ) - 2)) % 3 =
          hand n (⟨r.val, by omega⟩ : Rank n) % 3 := by
  have bound := r.isLt
  rw [hand_apply]
  dsimp only
  by_cases early : r.val ≤ 4
  · interval_cases position : r.val
    all_goals
      have parity : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases parity with parity | parity
      all_goals
        norm_num [baseSequence, parity]
        all_goals split_ifs <;> omega
  · rw [base_convolution_tail (by omega) (by omega) (by omega)]
    have not_zero : r.val ≠ 0 := by omega
    have not_one : r.val ≠ 1 := by omega
    have not_two : r.val ≠ 2 := by omega
    have not_three : r.val ≠ 3 := by omega
    have not_tail : ¬3 * n - 2 ≤ r.val := by omega
    have not_special : ¬(n % 2 = 1 ∧ r.val = 4) := by omega
    simp only [ite_eq_right not_zero, ite_eq_right not_one, ite_eq_right not_two,
      ite_eq_right not_three, ite_eq_right not_tail, ite_eq_right not_special]
    split_ifs <;> omega

lemma coefficient_sequenceCoefficients {n : ℕ} (i q : Rank n) (k : ℤ)
    (upper : k < (3 * n - 2 : ℕ)) : coefficient (sequenceCoefficients i q) k =
      (baseSequence ((n % 2 : ℕ) : ℤ) k + SequenceImpulse.value i.val k +
        SequenceImpulse.value q.val k) % 3 := by
  by_cases lower : 0 ≤ k
  · rw [coefficient, dite_eq_left ⟨lower, upper⟩]
    change (baseSequence ((n % 2 : ℕ) : ℤ) (k.toNat : ℤ) +
      SequenceImpulse.value i.val (k.toNat : ℤ) +
        SequenceImpulse.value q.val (k.toNat : ℤ)) % 3 = _
    have cast : (k.toNat : ℤ) = k := by omega
    rw [cast]
  · rw [coefficient_of_neg _ (by omega)]
    have before_i : ¬(i.val : ℤ) ≤ k := by omega
    have before_q : ¬(q.val : ℤ) ≤ k := by omega
    simp only [baseSequence, ite_eq_left (by omega : k < 0), SequenceImpulse.value,
      ite_eq_right before_i, ite_eq_right before_q]
    norm_num

private lemma coefficient_congruence {n : ℕ} (order : 2 ≤ n) (i q : Rank n)
    (r : Fin (3 * n - 2)) :
    (sequenceHand (sequenceCoefficients i q) (⟨r.val, by omega⟩ : Rank n) : ZMod 3) =
      ((hand n + single i - pair q) (⟨r.val, by omega⟩ : Rank n) : ZMod 3) := by
  have bound := r.isLt
  have base := base_congruence order r
  have draw := SequenceImpulse.convolution i.val r.val
  have pair := SequenceImpulse.convolution q.val r.val
  have draw_eq : (r.val : ℤ) = i.val ↔ r.val = i.val := by omega
  have pair_eq : (r.val : ℤ) = q.val ↔ r.val = q.val := by omega
  simp only [draw_eq] at draw
  simp only [pair_eq] at pair
  apply (ZMod.intCast_eq_intCast_iff' _ _ 3).mpr
  norm_num only [Nat.cast_ofNat]
  simp only [sequenceHand_apply, coefficient_sequenceCoefficients i q (r.val : ℤ) (by omega),
    coefficient_sequenceCoefficients i q ((r.val : ℤ) - 1) (by omega),
    coefficient_sequenceCoefficients i q ((r.val : ℤ) - 2) (by omega),
    Pi.sub_apply, Pi.add_apply, pair_apply, single_apply, Fin.ext_iff]
  omega

lemma canonicalSequence_formula {n : ℕ} (order : 2 ≤ n) (i q : Rank n)
    (r : Fin (3 * n - 2)) : canonicalSequence (hand n + single i - pair q) (r.val + 1) =
      sequenceCoefficients i q r := by
  let p : Placement n := ⟨sequenceCoefficients i q, 0⟩
  have canonical : p.Canonic := by
    intro s
    exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have same := (canonicalSequence_prefix_iff (hand n + single i - pair q) p.toHand
    (3 * n - 2) (by omega)).mp (by
      intro k before
      have equal := coefficient_congruence order i q ⟨k.val, before⟩
      simpa only [p, Placement.toHand_no_triplets] using equal.symm)
  rw [same (r.val + 1) (by omega), canonical.canonicalSequence_eq _ (by omega)]
  have index : ((r.val + 1 : ℕ) : ℤ) - 1 = r.val := by omega
  rw [index, coefficient_fin]

end Mahjong.VirtualHand.AlternatingWait
