/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Size
public import Ninegates.Wait.Graph

/-! The fixed classes of the even and odd alternating families are two and zero. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

lemma fixedClass_hand {n : ℕ} (order : 2 ≤ n) :
    fixedClass (hand n) = 2 + (n % 2 : ℕ) := by
  rw [fixedClass, hand_decomposition order]
  simp only [map_sub, map_add, map_smul, smul_eq_mul]
  rw [rankSum_singleAt (by omega), rankSum_singleAt (by omega), rankSum_singleAt (by omega),
    rankSum_singleAt (by omega), rankSum_singleAt (by omega), rankSum_singleAt (by omega),
    rankSum_singleAt (by omega)]
  have last : ((3 * n - 1 : ℕ) : ℤ) + 1 = 3 * (n : ℤ) := by omega
  rw [last]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  rw [rankSum_const_cast, rankSum_parityMatch_cast]
  have vanish : (3 : ZMod 3) * (3 + 2 * ((n % 2 : ℕ) : ZMod 3) +
      ((3 * n - 2 : ℕ) : ZMod 3) + 2 * (n : ZMod 3)) = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  linear_combination -vanish

lemma fixedClass_even (a : ℕ) : fixedClass (even a) = 2 := by
  rw [even, fixedClass_hand (by omega)]
  have parity : (2 * a + 2) % 2 = 0 := by omega
  rw [parity]
  norm_num

lemma fixedClass_odd (a : ℕ) : fixedClass (odd a) = 0 := by
  rw [odd, fixedClass_hand (by omega)]
  have parity : (2 * a + 3) % 2 = 1 := by omega
  rw [parity]
  decide +kernel

end Mahjong.VirtualHand.AlternatingWait
