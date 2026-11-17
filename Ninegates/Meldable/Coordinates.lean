/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Basic

/-!
# Coordinate equations of a meld placement

`coefficient s k` extends a finite coefficient vector by zero to integer indices.
Indices here are zero-based; in particular the two predecessor coordinates at
the left boundary are genuinely zero, not truncated natural-number indices.
The finite-sum implementation is hidden behind `Placement.toHand_apply`.
-/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n N : ℕ}

section Coefficient

variable {R : Type*} [Zero R]

def coefficient (s : Fin N → R) (k : ℤ) : R :=
  if h : 0 ≤ k ∧ k < N then s ⟨k.toNat, by omega⟩ else 0

@[grind =]
lemma coefficient_apply (s : Fin N → R) (k : ℤ) :
    coefficient s k = if h : 0 ≤ k ∧ k < N then s ⟨k.toNat, by omega⟩ else 0 := rfl

@[simp]
lemma coefficient_fin (s : Fin N → R) (i : Fin N) : coefficient s i.val = s i := by
  simp [coefficient, i.isLt]

@[simp]
lemma coefficient_of_neg (s : Fin N → R) {k : ℤ} (h : k < 0) : coefficient s k = 0 := by
  simp [coefficient, show ¬0 ≤ k by omega]

@[simp]
lemma coefficient_of_ge (s : Fin N → R) {k : ℤ} (h : (N : ℤ) ≤ k) :
    coefficient s k = 0 := by simp [coefficient, show ¬k < N by omega]

lemma coefficient_map {S : Type*} [Zero S] (s : Fin N → R) (f : R → S)
    (zero : f 0 = 0) (k : ℤ) : coefficient (fun i ↦ f (s i)) k = f (coefficient s k) := by
  unfold coefficient
  split <;> simp_all

lemma coefficient_restrict_lt (s : Fin N → R) (cut : ℕ) (k : ℤ) :
    coefficient (fun j ↦ if j.val < cut then s j else 0) k =
      if k < cut then coefficient s k else 0 := by
  unfold coefficient
  dsimp only
  split_ifs <;> first | rfl | omega

end Coefficient

lemma coefficient_nonnegative {s : Fin N → ℤ} (h : 0 ≤ s) (k : ℤ) :
    0 ≤ coefficient s k := by
  unfold coefficient
  split
  · exact h _
  · norm_num

@[simp]
lemma coefficient_intCast {R : Type*} [AddGroupWithOne R] (s : Fin N → ℤ) (k : ℤ) :
    coefficient (fun i ↦ (s i : R)) k = ((coefficient s k : ℤ) : R) :=
  coefficient_map s (fun z : ℤ ↦ (z : R)) (by simp) k

@[simp]
lemma coefficient_emod (s : Fin N → ℤ) (divisor k : ℤ) :
    coefficient (fun i ↦ s i % divisor) k = coefficient s k % divisor :=
  coefficient_map s (fun z ↦ z % divisor) (by simp) k

@[simp]
lemma coefficient_ediv (s : Fin N → ℤ) (divisor k : ℤ) :
    coefficient (fun i ↦ s i / divisor) k = coefficient s k / divisor :=
  coefficient_map s (fun z ↦ z / divisor) (by simp) k

/-- A zero-initialized three-term convolution is injective over any cancellative
additive monoid. This applies both to integer placements and to residues. -/
lemma coefficients_ext {R : Type*} [AddCancelCommMonoid R] (s t : Fin N → R)
    (same : ∀ i : Fin N, coefficient s i.val + coefficient s ((i.val : ℤ) - 1) +
      coefficient s ((i.val : ℤ) - 2) =
      coefficient t i.val + coefficient t ((i.val : ℤ) - 1) + coefficient t ((i.val : ℤ) - 2)) :
    s = t := by
  have all : ∀ k : ℕ, k < N → coefficient s (k : ℤ) = coefficient t (k : ℤ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro inside
      have previous (d : ℕ) (positive : 0 < d) :
          coefficient s ((k : ℤ) - d) = coefficient t ((k : ℤ) - d) := by
        by_cases enough : d ≤ k
        · have cast : (k : ℤ) - d = ((k - d : ℕ) : ℤ) := by omega
          rw [cast]
          exact ih (k - d) (by omega) (by omega)
        · rw [coefficient_of_neg s (by omega), coefficient_of_neg t (by omega)]
      have row := same ⟨k, inside⟩
      have one : coefficient s ((k : ℤ) - 1) = coefficient t ((k : ℤ) - 1) := by
        simpa using previous 1 (by decide)
      have two : coefficient s ((k : ℤ) - 2) = coefficient t ((k : ℤ) - 2) := by
        simpa using previous 2 (by decide)
      rw [one, two] at row
      exact add_right_cancel (add_right_cancel row)
  ext i
  simpa using all i.val i.isLt

private lemma sum_shift (s : Fin N → ℤ) (offset k : ℤ) :
    (∑ j : Fin N, if (j.val : ℤ) + offset = k then s j else 0) =
      coefficient s (k - offset) := by
  by_cases inside : 0 ≤ k - offset ∧ k - offset < N
  · let index : Fin N := ⟨(k - offset).toNat, by omega⟩
    have at_index : (index.val : ℤ) + offset = k := by dsimp [index]; omega
    rw [Finset.sum_eq_single index]
    · rw [ite_eq_left at_index, coefficient, dite_eq_left inside]
    · intro j _ different
      have absent : ¬(j.val : ℤ) + offset = k := by
        intro equal
        apply different
        apply Fin.ext
        dsimp [index]
        omega
      simp [absent]
    · simp
  · rw [coefficient, dite_eq_right inside]
    apply Finset.sum_eq_zero
    intro j _
    have absent : ¬(j.val : ℤ) + offset = k := by
      have bound := j.isLt
      omega
    simp [absent]

private lemma sum_shifted_single (s : Fin (3 * n - 2) → ℤ)
    (offset : ℕ) (bound : offset ≤ 2) (i : Rank n) :
    (∑ j : Fin (3 * n - 2), s j • single ⟨j.val + offset, by omega⟩) i =
      coefficient s ((i.val : ℤ) - offset) := by
  rw [← sum_shift s (offset : ℤ) (i.val : ℤ)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, single]
  apply Finset.sum_congr rfl
  intro j _
  have equal : (i = ⟨j.val + offset, by omega⟩) ↔ (j.val : ℤ)+offset = i.val := by
    rw [Fin.ext_iff]
    change i.val = j.val + offset ↔ (j.val : ℤ)+offset = i.val
    omega
  simp only [equal]
  split <;> simp_all

namespace Placement

@[simp, grind =]
lemma toHand_apply (p : Placement n) (i : Rank n) :
    p.toHand i = coefficient p.seqNum i.val + coefficient p.seqNum ((i.val : ℤ) - 1) +
      coefficient p.seqNum ((i.val : ℤ) - 2) + 3 * p.tripNum i := by
  have sequences : (∑ j, p.seqNum j • sequence j) =
      (∑ j : Fin (3 * n - 2), p.seqNum j • single ⟨j.val + 0, by omega⟩) +
      (∑ j : Fin (3 * n - 2), p.seqNum j • single ⟨j.val + 1, by omega⟩) +
      (∑ j : Fin (3 * n - 2), p.seqNum j • single ⟨j.val + 2, by omega⟩) := by
    simp [sequence, smul_add, Finset.sum_add_distrib]
  rw [toHand, sequences]
  simp only [Pi.add_apply]
  rw [sum_shifted_single p.seqNum 0 (by decide) i,
    sum_shifted_single p.seqNum 1 (by decide) i, sum_shifted_single p.seqNum 2 (by decide) i]
  simp [triplet, single, Finset.sum_apply, mul_ite, mul_comm]

end Placement
end Mahjong.VirtualHand
