/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Interval

/-! Explicit unique sequence updates for long moves in both directions. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

namespace Moving

/-- Signed sequence coefficients of a rightward move on integer indices. -/
def delta (a b k : ℤ) : ℤ :=
  if a ≤ k ∧ k < b then
    if (k - a) % 3 = 0 then -1 else if (k - a) % 3 = 1 then 1 else 0
  else 0

lemma delta_convolution (a b k : ℤ) (order : a ≤ b) (same : (b - a) % 3 = 0) :
    delta a b k + delta a b (k - 1) + delta a b (k - 2) =
      -(if k = a then 1 else 0) + (if k = b then 1 else 0) := by
  unfold delta
  split_ifs <;> omega

lemma coefficient_delta (i j : Rank n) (same : rankClass i = rankClass j) (k : ℤ) :
    coefficient (fun r : Fin (3 * n - 2) ↦ delta i.val j.val r.val) k =
      delta i.val j.val k := by
  have congruent := (rankClass_eq_iff i j).mp same
  have bound_i := i.isLt
  have bound_j := j.isLt
  have length : (↑(3 * n - 2) : ℤ) = 3 * n - 2 := by omega
  by_cases inside : 0 ≤ k ∧ k < (3 * n - 2 : ℕ)
  · simp only [coefficient, dite_eq_left inside]
    congr 1
    omega
  · rw [coefficient, dite_eq_right inside]
    unfold delta
    split_ifs <;> omega

/-- The explicit long-range update of the sequence placement. -/
def shiftAlong (s : Fin (3 * n - 2) → ℤ) (i j : Rank n) : Fin (3 * n - 2) → ℤ :=
  s + fun r ↦ delta i.val j.val r.val

/-- For a leftward move, subtract the rightward update from the target back
to the source: starts `j+1,j+4,...` become `j,j+3,...`. -/
def shiftAlongLeft (s : Fin (3 * n - 2) → ℤ) (i j : Rank n) : Fin (3 * n - 2) → ℤ :=
  s - fun r ↦ delta j.val i.val r.val

lemma sequenceHand_shiftAlong (s : Fin (3 * n - 2) → ℤ) (i j : Rank n)
    (order : i.val ≤ j.val) (same : rankClass i = rankClass j) :
    sequenceHand (shiftAlong s i j) = moveTile (sequenceHand s) i j := by
  have congruent : ((j.val : ℤ) - i.val) % 3 = 0 := by
    have := (rankClass_eq_iff i j).mp same
    omega
  rw [shiftAlong, map_add]
  ext k
  simp only [Pi.add_apply, sequenceHand_apply, coefficient_delta i j same, moveTile,
    Pi.sub_apply, single_apply, Fin.ext_iff]
  have identity := delta_convolution i.val j.val k.val (by omega) congruent
  have eq_i : (k.val : ℤ) = i.val ↔ k.val = i.val := by omega
  have eq_j : (k.val : ℤ) = j.val ↔ k.val = j.val := by omega
  simp only [eq_i, eq_j] at identity
  omega

lemma sequenceHand_shiftAlongLeft (s : Fin (3 * n - 2) → ℤ) (i j : Rank n)
    (order : j.val ≤ i.val) (same : rankClass i = rankClass j) :
    sequenceHand (shiftAlongLeft s i j) = moveTile (sequenceHand s) i j := by
  have backwards : sequenceHand (fun r : Fin (3 * n - 2) ↦ delta j.val i.val r.val) =
      moveTile 0 j i := by
    simpa only [shiftAlong, zero_add, map_zero] using
      sequenceHand_shiftAlong 0 j i order same.symm
  rw [shiftAlongLeft, map_sub, backwards]
  unfold moveTile
  abel

lemma shiftAlong_nonnegative_iff {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (i j : Rank n) :
    0 ≤ shiftAlong s i j ↔ ∀ r : Fin (3 * n - 2),
      i.val ≤ r.val → r.val < j.val → (r.val - i.val) % 3 = 0 → 1 ≤ s r := by
  constructor
  · intro result r lower upper congruent
    have at_r := result r
    have int_congruent : ((r.val : ℤ) - i.val) % 3 = 0 := by omega
    have inside : (i.val : ℤ) ≤ r.val ∧ (r.val : ℤ) < j.val := by omega
    change 0 ≤ s r + delta i.val j.val r.val at at_r
    rw [delta, ite_eq_left inside, ite_eq_left int_congruent] at at_r
    omega
  · intro required r
    have original : 0 ≤ s r := positive r
    change 0 ≤ s r + delta i.val j.val r.val
    unfold delta
    split_ifs with inside residue
    · have needed := required r (by omega) (by omega) (by omega)
      omega
    · omega
    · omega
    · omega

lemma shiftAlongLeft_nonnegative_iff {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (i j : Rank n) :
    0 ≤ shiftAlongLeft s i j ↔ ∀ r : Fin (3 * n - 2),
      j.val ≤ r.val → r.val < i.val → (r.val - j.val) % 3 = 1 → 1 ≤ s r := by
  constructor
  · intro result r lower upper congruent
    have at_r := result r
    have int_congruent : ((r.val : ℤ) - j.val) % 3 = 1 := by omega
    have not_zero : ((r.val : ℤ) - j.val) % 3 ≠ 0 := by omega
    have inside : (j.val : ℤ) ≤ r.val ∧ (r.val : ℤ) < i.val := by omega
    change 0 ≤ s r - delta j.val i.val r.val at at_r
    rw [delta, ite_eq_left inside, ite_eq_right not_zero, ite_eq_left int_congruent] at at_r
    omega
  · intro required r
    have original : 0 ≤ s r := positive r
    change 0 ≤ s r - delta j.val i.val r.val
    unfold delta
    split_ifs with inside zero one
    · omega
    · have needed := required r (by omega) (by omega) (by omega)
      omega
    · omega
    · omega

end Moving

/-- `prp-tile-moving`, rightward direction. The required starts are exactly
`i, i+3, ..., j-3`; the replacement starts are one rank to their right. -/
lemma sequential_moveTile_right_iff {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (i j : Rank n) (order : i.val ≤ j.val) :
    Sequential (moveTile (sequenceHand s) i j) ↔ rankClass i = rankClass j ∧
      ∀ r : Fin (3 * n - 2), i.val ≤ r.val → r.val < j.val →
        (r.val - i.val) % 3 = 0 → 1 ≤ s r := by
  have base : Meldable (sequenceHand s) := Sequential.meldable ⟨s, positive, rfl⟩
  constructor
  · intro result
    have same := base.virtuallyMeldable.moveTile_rankClass result.meldable.virtuallyMeldable
    refine ⟨same, ?_⟩
    obtain ⟨t, ht, equal⟩ := result
    have unique := sequenceHand_injective
      (equal.trans (Moving.sequenceHand_shiftAlong s i j order same).symm)
    exact (Moving.shiftAlong_nonnegative_iff positive i j).mp (unique ▸ ht)
  · rintro ⟨same, required⟩
    exact ⟨Moving.shiftAlong s i j,
      (Moving.shiftAlong_nonnegative_iff positive i j).mpr required,
      Moving.sequenceHand_shiftAlong s i j order same⟩

/-- `prp-tile-moving`, leftward direction. Required starts are
`j+1, j+4, ..., i-2`, and their replacements are one rank to the left. -/
lemma sequential_moveTile_left_iff {s : Fin (3 * n - 2) → ℤ} (positive : 0 ≤ s)
    (i j : Rank n) (order : j.val ≤ i.val) :
    Sequential (moveTile (sequenceHand s) i j) ↔ rankClass i = rankClass j ∧
      ∀ r : Fin (3 * n - 2), j.val ≤ r.val → r.val < i.val →
        (r.val - j.val) % 3 = 1 → 1 ≤ s r := by
  have base : Meldable (sequenceHand s) := Sequential.meldable ⟨s, positive, rfl⟩
  constructor
  · intro result
    have same := base.virtuallyMeldable.moveTile_rankClass result.meldable.virtuallyMeldable
    refine ⟨same, ?_⟩
    obtain ⟨t, ht, equal⟩ := result
    have unique := sequenceHand_injective
      (equal.trans (Moving.sequenceHand_shiftAlongLeft s i j order same).symm)
    exact (Moving.shiftAlongLeft_nonnegative_iff positive i j).mp (unique ▸ ht)
  · rintro ⟨same, required⟩
    exact ⟨Moving.shiftAlongLeft s i j,
      (Moving.shiftAlongLeft_nonnegative_iff positive i j).mpr required,
      Moving.sequenceHand_shiftAlongLeft s i j order same⟩

end Mahjong.VirtualHand
