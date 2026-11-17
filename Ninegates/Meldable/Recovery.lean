/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Sequence
public import Ninegates.Hand.Classes

/-!
# Recovering sequence coefficients

The generic recurrence takes values in an additive commutative group. Its
integer instance recovers a virtual sequence placement; its residue instance
will provide the canonical scan. The state after `k` ranks is `(σ_k,σ_{k-1})`,
with both initial values zero.
-/

@[expose] public section

namespace Mahjong.VirtualHand.SequenceScan

variable {R : Type*} [AddCommGroup R]

def run (a : ℕ → R) : ℕ → R × R
  | 0 => (0, 0)
  | k + 1 =>
      let previous := run a k
      (a k - previous.1 - previous.2, previous.1)

@[simp]
lemma run_zero (a : ℕ → R) : run a 0 = (0, 0) := rfl

@[simp]
lemma run_snd_succ (a : ℕ → R) (k : ℕ) : (run a (k + 1)).2 = (run a k).1 := rfl

lemma input_eq (a : ℕ → R) (k : ℕ) :
    a k = (run a (k + 1)).1 + (run a k).1 + (run a k).2 := by
  simp only [run]
  abel

lemma run_congr {a b : ℕ → R} (k : ℕ) (same : ∀ j < k, a j = b j) : run a k = run b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [run, same k (by omega), ih (fun j hj ↦ same j (by omega))]

lemma run_three (a : ℕ → R) (k : ℕ) : run a (k + 3) =
    ((run a k).1 + a (k + 2) - a (k + 1), (run a k).2 + a (k + 1) - a k) := by
  simp only [run]
  ext <;> abel_nf

lemma run_blocks (a : ℕ → R) (n : ℕ) : run a (3 * n) =
    ((∑ b ∈ Finset.range n, (a (3 * b + 2) - a (3 * b + 1))),
     (∑ b ∈ Finset.range n, (a (3 * b + 1) - a (3 * b)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, run_three, ih]
      simp only [Finset.sum_range_succ, sub_eq_add_neg, add_assoc]

lemma run_of_coefficients {N : ℕ} (s : Fin N → R) (k : ℕ) :
    run (fun j ↦ coefficient s (j : ℤ) + coefficient s ((j : ℤ) - 1) +
      coefficient s ((j : ℤ) - 2)) k =
      (coefficient s ((k : ℤ) - 1), coefficient s ((k : ℤ) - 2)) := by
  induction k with
  | zero => simp [coefficient]
  | succ k ih =>
      rw [run, ih]
      have one : (k : ℤ) + 1-1 = k := by omega
      have two : (k : ℤ) + 1-2 = (k : ℤ) - 1 := by omega
      simp only [Nat.cast_add, Nat.cast_one, one, two]
      ext <;> abel_nf

end Mahjong.VirtualHand.SequenceScan

namespace Mahjong.VirtualHand

variable {n : ℕ}

def sequenceScan (c : VirtualHand n) : ℕ → ℤ × ℤ :=
  SequenceScan.run fun k ↦ coefficient c (k : ℤ)

def recoveredSequences (c : VirtualHand n) : Fin (3 * n - 2) → ℤ :=
  fun j ↦ (sequenceScan c (j.val + 1)).1

private def recoveryTerm (c : VirtualHand n) (j t : ℕ) : ℤ :=
  coefficient c ((j : ℤ) - 1 - 3 * t) - coefficient c ((j : ℤ) - 2 - 3 * t)

/-- The closed form `σ_j = (c_j-c_{j-1}) + (c_{j-3}-c_{j-4}) + ...`,
with zero extension at the left boundary. -/
lemma sequenceScan_closed_form (c : VirtualHand n) (j : ℕ) :
    (sequenceScan c j).1 = ∑ t ∈ Finset.range ((j + 2) / 3),
      (coefficient c ((j : ℤ) - 1 - 3 * t) - coefficient c ((j : ℤ) - 2 - 3 * t)) := by
  change (sequenceScan c j).1 = ∑ t ∈ Finset.range ((j + 2) / 3), recoveryTerm c j t
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [sequenceScan]
    | succ j =>
      cases j with
      | zero => norm_num [sequenceScan, SequenceScan.run, recoveryTerm]
      | succ j =>
        cases j with
        | zero => norm_num [sequenceScan, SequenceScan.run, recoveryTerm]
        | succ k =>
          have shift (t : ℕ) : recoveryTerm c (k + 3) (t + 1) = recoveryTerm c k t := by
            unfold recoveryTerm
            push_cast
            congr 1 <;> congr 1 <;> omega
          have head : recoveryTerm c (k + 3) 0 =
              coefficient c ((k + 2 : ℕ) : ℤ) - coefficient c ((k + 1 : ℕ) : ℤ) := by
            unfold recoveryTerm
            push_cast
            congr 1 <;> congr 1 <;> omega
          have steps : (k + 3 + 2) / 3 = (k + 2) / 3 + 1 := by omega
          have recurrence := congrArg Prod.fst
            (SequenceScan.run_three (fun i ↦ coefficient c (i : ℤ)) k)
          change (sequenceScan c (k + 3)).1 = (sequenceScan c k).1 +
            coefficient c ((k + 2 : ℕ) : ℤ) - coefficient c ((k + 1 : ℕ) : ℤ) at recurrence
          change (sequenceScan c (k + 3)).1 = _
          rw [recurrence, ih k (by omega), steps, Finset.sum_range_succ']
          simp only [shift, head]
          abel

private lemma class_block_sum (c : VirtualHand n) (r : Fin 3) :
    (∑ k ∈ Finset.range n, coefficient c ((3 * k + r.val : ℕ) : ℤ)) =
      ∑ b : Fin n, c (blockEquiv n (b, r)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b _
  rw [← blockEquiv_val b r, coefficient_fin]

/-- The two boundary coordinates in `prp-virtual-seq-placement`. -/
lemma sequenceScan_boundary (c : VirtualHand n) : sequenceScan c (3 * n) =
    (classSize 0 c - classSize 2 c, classSize 2 c - classSize 1 c) := by
  rw [sequenceScan, SequenceScan.run_blocks]
  simp only [Finset.sum_sub_distrib]
  have zero : (∑ k ∈ Finset.range n, coefficient c ((3 * k : ℕ) : ℤ)) =
      ∑ b : Fin n, c (blockEquiv n (b, 0)) := by simpa using class_block_sum c 0
  have one : (∑ k ∈ Finset.range n, coefficient c ((3 * k + 1 : ℕ) : ℤ)) =
      ∑ b : Fin n, c (blockEquiv n (b, 1)) := by simpa using class_block_sum c 1
  have two : (∑ k ∈ Finset.range n, coefficient c ((3 * k + 2 : ℕ) : ℤ)) =
      ∑ b : Fin n, c (blockEquiv n (b, 2)) := by simpa using class_block_sum c 2
  rw [two, one, zero]
  rw [classSize_zero_blocks, classSize_two_blocks, classSize_one_blocks]

lemma sequenceScan_sequenceHand (s : Fin (3 * n - 2) → ℤ) (k : ℕ) (bound : k ≤ 3 * n) :
    sequenceScan (sequenceHand s) k =
      (coefficient s ((k : ℤ) - 1), coefficient s ((k : ℤ) - 2)) := by
  have same : ∀ j < k, coefficient (sequenceHand s) (j : ℤ) =
      coefficient s (j : ℤ) + coefficient s ((j : ℤ) - 1) + coefficient s ((j : ℤ) - 2) := by
    intro j inside
    let i : Rank n := ⟨j, by omega⟩
    change coefficient (sequenceHand s) i.val = _
    rw [coefficient_fin, sequenceHand_apply]
  exact (SequenceScan.run_congr k same).trans (SequenceScan.run_of_coefficients s k)

lemma sequenceScan_sequenceHand_end (s : Fin (3 * n - 2) → ℤ) :
    sequenceScan (sequenceHand s) (3 * n) = (0, 0) := by
  cases n with
  | zero => simp [sequenceScan]
  | succ n =>
      rw [sequenceScan_sequenceHand s _ (le_refl _),
        coefficient_of_ge s (by omega), coefficient_of_ge s (by omega)]

lemma recoveredSequences_reconstruct {c : VirtualHand n} (ends : sequenceScan c (3 * n) = (0, 0)) :
    sequenceHand (recoveredSequences c) = c := by
  let s := recoveredSequences c
  have current (k : ℕ) (inside : k < 3 * n) :
      coefficient s (k : ℤ) = (sequenceScan c (k + 1)).1 := by
    by_cases valid : k < 3 * n - 2
    · let j : Fin (3 * n - 2) := ⟨k, valid⟩
      change coefficient s j.val = _
      rw [coefficient_fin]
      rfl
    · rw [coefficient_of_ge s (by omega)]
      by_cases last : k + 1 = 3 * n
      · have zero := congrArg Prod.fst ends
        rw [← last] at zero
        exact zero.symm
      · have penultimate : k + 2 = 3 * n := by omega
        have zero := congrArg Prod.snd ends
        rw [← penultimate] at zero
        exact zero.symm
  have before (k : ℕ) (inside : k ≤ 3 * n) :
      coefficient s ((k : ℤ) - 1) = (sequenceScan c k).1 := by
    cases k with
    | zero => simp [sequenceScan]
    | succ k =>
        have index : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
        rw [index]
        exact current k (by omega)
  have older (k : ℕ) (inside : k ≤ 3 * n) :
      coefficient s ((k : ℤ) - 2) = (sequenceScan c k).2 := by
    cases k with
    | zero => simp [sequenceScan]
    | succ k =>
        have index : ((k + 1 : ℕ) : ℤ) - 2 = (k : ℤ) - 1 := by omega
        rw [index]
        exact before k (by omega)
  ext i
  change sequenceHand s i = c i
  rw [sequenceHand_apply, current i.val i.isLt, before i.val (by omega), older i.val (by omega)]
  have recovered := SequenceScan.input_eq (fun k ↦ coefficient c (k : ℤ)) i.val
  rw [coefficient_fin] at recovered
  exact recovered.symm

lemma virtuallySequential_iff_scan (c : VirtualHand n) :
    VirtuallySequential c ↔ sequenceScan c (3 * n) = (0, 0) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact sequenceScan_sequenceHand_end s
  · intro ends
    exact ⟨recoveredSequences c, recoveredSequences_reconstruct ends⟩

/-- The existence criterion in `prp-virtual-seq-placement`. Uniqueness is
`VirtuallySequential.unique`. -/
lemma virtuallySequential_iff_classSizes (c : VirtualHand n) :
    VirtuallySequential c ↔ classSize 0 c = classSize 1 c ∧ classSize 1 c = classSize 2 c := by
  rw [virtuallySequential_iff_scan, sequenceScan_boundary]
  simp only [Prod.mk.injEq, sub_eq_zero]
  omega

@[simp]
lemma recoveredSequences_sequenceHand (s : Fin (3 * n - 2) → ℤ) :
    recoveredSequences (sequenceHand s) = s :=
  sequenceHand_injective (recoveredSequences_reconstruct (sequenceScan_sequenceHand_end s))

/-- The nonnegative sequence-placement criterion, for unrestricted meld count. -/
lemma sequential_iff_classSizes (c : VirtualHand n) : Sequential c ↔
    (classSize 0 c = classSize 1 c ∧ classSize 1 c = classSize 2 c) ∧
      0 ≤ recoveredSequences c := by
  constructor
  · rintro ⟨s, nonnegative, rfl⟩
    exact ⟨(virtuallySequential_iff_classSizes _).mp ⟨s, rfl⟩, by simpa using nonnegative⟩
  · rintro ⟨classes, nonnegative⟩
    have virtual := (virtuallySequential_iff_classSizes c).mpr classes
    exact ⟨recoveredSequences c, nonnegative,
      recoveredSequences_reconstruct ((virtuallySequential_iff_scan c).mp virtual)⟩

end Mahjong.VirtualHand
