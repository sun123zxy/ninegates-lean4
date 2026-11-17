/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Basic

/-! Linear restrictions to the ranks strictly before or after a cut. Both
pieces retain the original rank space, so cuts need not be multiples of three. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def leftOf (k : Rank n) : VirtualHand n →ₗ[ℤ] VirtualHand n where
  toFun c i := if i.val < k.val then c i else 0
  map_add' _ _ := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' _ _ := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

def rightOf (k : Rank n) : VirtualHand n →ₗ[ℤ] VirtualHand n where
  toFun c i := if k.val < i.val then c i else 0
  map_add' _ _ := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' _ _ := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[grind =]
lemma leftOf_apply (k : Rank n) (c : VirtualHand n) (i : Rank n) :
    leftOf k c i = if i.val < k.val then c i else 0 := rfl

@[grind =]
lemma rightOf_apply (k : Rank n) (c : VirtualHand n) (i : Rank n) :
    rightOf k c i = if k.val < i.val then c i else 0 := rfl

@[grind =]
lemma leftOf_single (k i : Rank n) :
    leftOf k (single i) = if i.val < k.val then single i else 0 := by
  ext j
  simp only [leftOf_apply, ite_apply, Pi.zero_apply, single_apply]
  grind

@[grind =]
lemma rightOf_single (k i : Rank n) :
    rightOf k (single i) = if k.val < i.val then single i else 0 := by
  ext j
  simp only [rightOf_apply, ite_apply, Pi.zero_apply, single_apply]
  grind

@[grind =]
lemma leftOf_pair (k i : Rank n) :
    leftOf k (pair i) = if i.val < k.val then pair i else 0 := by
  rw [pair, map_smul, leftOf_single]
  split_ifs <;> simp

@[grind =]
lemma rightOf_pair (k i : Rank n) :
    rightOf k (pair i) = if k.val < i.val then pair i else 0 := by
  rw [pair, map_smul, rightOf_single]
  split_ifs <;> simp

lemma leftOf_add_rightOf (c : VirtualHand n) (k : Rank n) (missing : c k = 0) :
    leftOf k c + rightOf k c = c := by
  ext i
  simp only [Pi.add_apply, leftOf_apply, rightOf_apply]
  by_cases equal : i = k
  · subst i
    simp [missing]
  · have different : i.val ≠ k.val := fun h ↦ equal (Fin.ext h)
    split_ifs <;> simp_all <;> omega

@[simp]
lemma leftOf_reverse (c : VirtualHand n) (k : Rank n) :
    leftOf k.rev (reverse c) = reverse (rightOf k c) := by
  ext i
  have bound_i := i.isLt
  have bound_k := k.isLt
  simp only [leftOf_apply, rightOf_apply, reverse_apply, Fin.val_rev]
  have order : i.val < 3 * n - (k.val + 1) ↔ k.val < 3 * n - (i.val + 1) := by omega
  simp only [order]

@[simp]
lemma rightOf_reverse (c : VirtualHand n) (k : Rank n) :
    rightOf k.rev (reverse c) = reverse (leftOf k c) := by
  have reflected := leftOf_reverse (reverse c) k.rev
  simpa using (congrArg reverse reflected).symm

end Mahjong.VirtualHand
