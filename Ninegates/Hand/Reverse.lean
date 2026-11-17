/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Basic
public import Mathlib.Data.Fin.Rev

/-! Reversal preserves size and sends the one-based rank sum to
`(3*n+1)*size-rankSum`. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma Nonnegative.reverse {c : VirtualHand n} (h : Nonnegative c) : Nonnegative (reverse c) :=
  fun i ↦ h i.rev

lemma Bounded.reverse {cap : ℕ} {c : VirtualHand n} (h : Bounded cap c) :
    Bounded cap (VirtualHand.reverse c) := ⟨h.1.reverse, fun i ↦ h.2 i.rev⟩

lemma Valid.reverse {c : VirtualHand n} (h : Valid c) : Valid (VirtualHand.reverse c) :=
  Bounded.reverse h

@[simp]
lemma size_reverse (c : VirtualHand n) : size (reverse c) = size c := by
  change (∑ i : Rank n, c i.rev) = ∑ i, c i
  simpa only [Fin.revPerm_apply] using Equiv.sum_comp (Fin.revPerm (n := 3 * n)) c

lemma rank_rev (i : Rank n) : rank i.rev = 3 * (n : ℤ) + 1 - rank i := by
  unfold rank
  have bound := i.isLt
  simp only [Fin.val_rev]
  omega

lemma rankClass_rev (i : Rank n) : rankClass i.rev = 1 - rankClass i := by
  rw [rankClass, rank_rev]
  push_cast
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
  rfl

@[simp]
lemma classSize_reverse (c : VirtualHand n) (r : ZMod 3) :
    classSize r (reverse c) = classSize (1 - r) c := by
  simp only [classSize, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_filter]
  calc
    _ = ∑ i : Rank n, if rankClass i.rev = r then c i else 0 := by
      simpa only [Fin.revPerm_apply, Fin.rev_rev, reverse_apply] using
        (Equiv.sum_comp (Fin.revPerm (n := 3 * n))
          (fun i ↦ if rankClass i = r then c i.rev else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have equal : rankClass i.rev = r ↔ rankClass i = 1 - r := by
        rw [rankClass_rev]
        constructor <;> intro same <;> linear_combination -same
      simp only [equal]

lemma rankSum_reverse (c : VirtualHand n) :
    rankSum (reverse c) = (3 * (n : ℤ) + 1) * size c - rankSum c := by
  calc
    _ = ∑ i : Rank n, rank i.rev * c i := by
      change (∑ i : Rank n, rank i * c i.rev) = _
      simpa only [Fin.revPerm_apply, Fin.rev_rev] using
        (Equiv.sum_comp (Fin.revPerm (n := 3 * n)) (fun i ↦ rank i * c i.rev)).symm
    _ = _ := by
      simp only [rank_rev, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl

end Mahjong.VirtualHand
