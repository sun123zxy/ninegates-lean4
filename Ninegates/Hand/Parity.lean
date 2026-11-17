/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Size
public import Ninegates.Hand.Classes

/-! Counting alternating coordinates on the `3n` ranks. -/

@[expose] public section

namespace Mahjong.VirtualHand

def parityMatch (n : ℕ) : VirtualHand n := fun i ↦ if (i.val + n) % 2 = 0 then 1 else 0

@[grind =]
lemma parityMatch_apply {n : ℕ} (i : Rank n) :
    parityMatch n i = if (i.val + n) % 2 = 0 then 1 else 0 := rfl

private def parityIndex (n : ℕ) (t : Fin (3 * n / 2)) : Rank n :=
  ⟨2 * t.val + n % 2, by have := t.isLt; omega⟩

private lemma parityIndex_injective (n : ℕ) : Function.Injective (parityIndex n) := by
  intro a b equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [parityIndex] at values
  omega

private lemma parity_indices (n : ℕ) :
    Finset.univ.filter (fun i : Rank n ↦ (i.val + n) % 2 = 0) =
      Finset.univ.image (parityIndex n) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro member
    refine ⟨⟨i.val / 2, by have := i.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [parityIndex]
    omega
  · rintro ⟨t, rfl⟩
    dsimp only [parityIndex]
    omega

lemma size_parityMatch (n : ℕ) : size (parityMatch n) = (3 * n / 2 : ℕ) := by
  change (∑ i : Rank n, if (i.val + n) % 2 = 0 then (1 : ℤ) else 0) = _
  rw [← Finset.sum_filter, parity_indices]
  simp [Finset.card_image_of_injective _ (parityIndex_injective n)]

private lemma sum_affine (k : ℕ) (b : ℤ) :
    (∑ t ∈ Finset.range k, (2 * (t : ℤ) + b + 1)) = (k : ℤ) * (k + b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma rankSum_parityMatch (n : ℕ) :
    rankSum (parityMatch n) = (3 * n / 2 : ℕ) * ((3 * n / 2 : ℕ) + ((n % 2 : ℕ) : ℤ)) := by
  change (∑ i : Rank n, rank i * (if (i.val + n) % 2 = 0 then (1 : ℤ) else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, parity_indices, Finset.sum_image]
  · simp only [rank, parityIndex]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ ↦ 2 * (t : ℤ) + ((n % 2 : ℕ) : ℤ) + 1)]
    exact sum_affine _ _
  · intro a _ b _ equal
    exact parityIndex_injective n equal

lemma rankSum_const_cast {n : ℕ} (z : ℤ) :
    (rankSum (fun _ : Rank n ↦ z) : ZMod 3) = 0 := by
  rw [rankSum_cast_eq_classSizes, classSize_const, classSize_const]
  push_cast
  have zero : (3 : ZMod 3) * ((n : ZMod 3) * (z : ZMod 3)) = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  linear_combination zero

lemma rankSum_parityMatch_cast (n : ℕ) :
    (rankSum (parityMatch n) : ZMod 3) = 2 * (n % 2 : ℕ) := by
  have half : 3 * n / 2 = 3 * (n / 2) + n % 2 := by
    have parity : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases parity with parity | parity <;> omega
  have residue : (3 * n / 2) % 3 = n % 2 := by rw [half]; omega
  have same : ((3 * n / 2 : ℕ) : ZMod 3) = (n % 2 : ℕ) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ 3).mpr
    omega
  rw [rankSum_parityMatch]
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast]
  rw [same]
  have parity : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases parity with parity | parity <;> rw [parity] <;> norm_num

end Mahjong.VirtualHand
