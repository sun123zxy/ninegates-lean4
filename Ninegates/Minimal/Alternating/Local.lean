/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.PrefixModel

/-! Kernel certificates for the exceptional triplets in the short prefix. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

private lemma prefix_certificate (b : Fin 2) (draw : Fin 6) (q : Fin 3)
    (allowed : draw.val = 5 ∨ (draw.val + q.val + b.val) % 3 = 2) :
    0 ≤ canonicalTriplet (PrefixModel.winning draw q) 3 ∧
      (b.val = 1 → 0 ≤ canonicalTriplet (PrefixModel.winning draw q) 4) := by
  fin_cases b <;> fin_cases draw <;> fin_cases q <;> norm_num at allowed <;> decide +kernel

lemma prefix_triplets_nonnegative {n : ℕ} (order : 2 ≤ n) (i q : Rank n) (small : q.val < 3)
    (congruent : (i.val + q.val + n % 2) % 3 = 2) :
    0 ≤ canonicalTriplet (hand n + single i - pair q) ⟨3, by omega⟩ ∧
      (n % 2 = 1 → 0 ≤ canonicalTriplet (hand n + single i - pair q) ⟨4, by omega⟩) := by
  have allowed : min i.val 5 = 5 ∨ (min i.val 5 + q.val + n % 2) % 3 = 2 := by
    by_cases early : i.val < 5
    · right
      have minimum : min i.val 5 = i.val := Nat.min_eq_left (by omega)
      simpa only [minimum] using congruent
    · left
      omega
  have certificate := prefix_certificate ⟨n % 2, by omega⟩
    ⟨min i.val 5, by omega⟩ ⟨q.val, small⟩ allowed
  constructor
  · rw [canonicalTriplet_eq_of_coefficient_prefix _ _ (⟨3, by omega⟩ : Rank n) (3 : Rank 2) rfl
      (PrefixModel.agree order i q small 3 (by omega) (by omega))]
    exact certificate.1
  · intro odd
    rw [canonicalTriplet_eq_of_coefficient_prefix _ _ (⟨4, by omega⟩ : Rank n) (4 : Rank 2) rfl
      (PrefixModel.agree order i q small 4 (by omega) (by intro; exact odd))]
    exact certificate.2 odd

end Mahjong.VirtualHand.AlternatingWait
