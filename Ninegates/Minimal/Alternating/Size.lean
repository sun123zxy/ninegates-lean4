/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Defs

/-! Sizes of the alternating families, obtained by counting the parity indicator. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

set_option maxHeartbeats 500000 in
-- The two parities and six position cases require many small arithmetic calls.
lemma hand_decomposition {n : ℕ} (order : 2 ≤ n) : hand n =
    (fun _ ↦ 4) + parityMatch n - (3 - ((n % 2 : ℕ) : ℤ)) • singleAt 0 -
      ((n % 2 : ℕ) : ℤ) • singleAt 1 + (1 + ((n % 2 : ℕ) : ℤ)) • singleAt 2 -
      (1 + ((n % 2 : ℕ) : ℤ)) • singleAt 3 - ((n % 2 : ℕ) : ℤ) • singleAt 4 -
      (3 : ℤ) • singleAt (3 * n - 2) - (2 : ℤ) • singleAt (3 * n - 1) := by
  ext i
  have bound := i.isLt
  have positions : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ 5 ≤ i.val := by omega
  simp only [hand_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    parityMatch_apply, singleAt_apply]
  have parity : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases parity with parity | parity
  all_goals
    norm_num only [parity]
    rcases positions with position | position | position | position | position | position
    all_goals norm_num only [position]; split_ifs <;> norm_num at * <;> omega

lemma size_hand {n : ℕ} (order : 2 ≤ n) : size (hand n) = 3 * (meldCount n : ℤ) + 1 := by
  rw [hand_decomposition order]
  simp only [map_sub, map_add, map_smul, size_const, size_parityMatch, smul_eq_mul]
  rw [size_singleAt (by omega), size_singleAt (by omega), size_singleAt (by omega),
    size_singleAt (by omega), size_singleAt (by omega), size_singleAt (by omega),
    size_singleAt (by omega)]
  simp only [mul_one]
  unfold meldCount
  have parity : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases parity with parity | parity <;> omega

lemma size_even (a : ℕ) : size (even a) = 3 * (9 * (a : ℤ) + 6) + 1 := by
  rw [even, size_hand (by omega)]
  unfold meldCount
  omega

lemma size_odd (a : ℕ) : size (odd a) = 3 * (9 * (a : ℤ) + 10) + 1 := by
  rw [odd, size_hand (by omega)]
  unfold meldCount
  omega

end Mahjong.VirtualHand.AlternatingWait
