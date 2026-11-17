/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Basic

/-! Size bounds and detection of the zero hand under nonnegativity. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

lemma Nonnegative.size_eq_zero_iff (positive : Nonnegative c) : size c = 0 ↔ c = 0 := by
  constructor
  · intro count
    ext i
    have bound := Finset.single_le_sum (fun j _ ↦ positive j) (Finset.mem_univ i)
    change c i ≤ size c at bound
    rw [count] at bound
    exact le_antisymm bound (positive i)
  · rintro rfl
    exact map_zero size

lemma Nonnegative.size_pos (positive : Nonnegative c) (nonzero : c ≠ 0) : 0 < size c := by
  have lower := positive.size_nonnegative
  have different := mt positive.size_eq_zero_iff.mp nonzero
  omega

lemma size_const (z : ℤ) : size (fun _ : Rank n ↦ z) = 3 * (n : ℤ) * z := by
  simp [size]

lemma Bounded.size_le {cap : ℕ} (bound : Bounded cap c) : size c ≤ 3 * (n : ℤ) * cap := by
  calc
    _ ≤ size (fun _ : Rank n ↦ (cap : ℤ)) := by
      change (∑ i, c i) ≤ ∑ _ : Rank n, (cap : ℤ)
      exact Finset.sum_le_sum (fun i _ ↦ bound.2 i)
    _ = _ := size_const _

end Mahjong.VirtualHand
