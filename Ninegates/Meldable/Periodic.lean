/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Segment

/-! Period-three sequence vectors and their hand prefixes. -/

@[expose] public section

namespace Mahjong.VirtualHand

namespace Periodic

def value (a b c k : ℤ) : ℤ := if k % 3 = 0 then a else if k % 3 = 1 then b else c

lemma convolution (a b c k : ℤ) :
    value a b c k + value a b c (k - 1) + value a b c (k - 2) = a + b + c := by
  unfold value
  split_ifs <;> omega

lemma coefficient_value {N : ℕ} (a b c k : ℤ) :
    coefficient (fun j : Fin N ↦ value a b c j.val) k =
      if 0 ≤ k ∧ k < N then value a b c k else 0 := by
  unfold coefficient
  split_ifs with inside
  · change value a b c (k.toNat : ℤ) = value a b c k
    congr 1
    omega
  · rfl

lemma sequenceHand_prefix {n : ℕ} (a b c : ℤ) (i : Rank n) (upper : i.val < 3 * n - 2) :
    sequenceHand (fun j : Fin (3 * n - 2) ↦ value a b c j.val) i =
      if i.val = 0 then a else if i.val = 1 then a + b else a + b + c := by
  have bound := i.isLt
  simp only [sequenceHand_apply, coefficient_value]
  by_cases first : i.val = 0
  · simp [first, value, show 0 < 3 * n - 2 by omega]
  · by_cases second : i.val = 1
    · have length : 1 < 3 * n - 2 := by omega
      simp [second, value, length, show 0 < 3 * n - 2 by omega, add_comm]
    · have current : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < (3 * n - 2 : ℕ) := by omega
      have previous : 0 ≤ (i.val : ℤ) - 1 ∧ (i.val : ℤ) - 1 < (3 * n - 2 : ℕ) := by omega
      have older : 0 ≤ (i.val : ℤ) - 2 ∧ (i.val : ℤ) - 2 < (3 * n - 2 : ℕ) := by omega
      simp only [ite_eq_left current, ite_eq_left previous, ite_eq_left older,
        ite_eq_right first, ite_eq_right second]
      exact convolution a b c i.val

lemma sequenceHand_twos {n : ℕ} :
    sequenceHand (fun j : Fin (3 * n - 2) ↦ value 2 0 0 j.val) = fun _ : Rank n ↦ 2 := by
  have representation := Segment.sequenceHand_starts (n := n) (a := 0) (b := 3 * n)
    (by omega) (by omega) (by omega)
  have equal : (fun j : Fin (3 * n - 2) ↦ value 2 0 0 j.val) =
      (2 : ℤ) • (fun j : Fin (3 * n - 2) ↦ Segment.starts 0 (3 * n) j.val) := by
    ext j
    have bound := j.isLt
    simp only [Pi.smul_apply, smul_eq_mul, value, Segment.starts]
    split_ifs <;> omega
  rw [equal, map_smul]
  have cast : (↑(3 * n) : ℤ) = 3 * n := by push_cast; rfl
  norm_num only [Nat.cast_zero] at representation
  rw [cast] at representation
  rw [representation]
  ext i
  have bound := i.isLt
  simp only [Pi.smul_apply, smul_eq_mul, segment_apply]
  rw [ite_eq_left (by omega)]
  norm_num

end Periodic
end Mahjong.VirtualHand
