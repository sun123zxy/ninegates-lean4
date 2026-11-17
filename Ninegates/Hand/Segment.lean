/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Reverse
public import Ninegates.Hand.Interior

/-! Single tiles at natural indices and intervals of single tiles. These make
the standard families meaningful without dependent bounds in their definitions. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def singleAt (k : ℕ) : VirtualHand n := fun i ↦ if i.val = k then 1 else 0

@[grind =]
lemma singleAt_apply (k : ℕ) (i : Rank n) : singleAt k i = if i.val = k then 1 else 0 := rfl

lemma singleAt_eq_single (i : Rank n) : singleAt i.val = single i := by
  ext j
  simp only [singleAt, single, Fin.ext_iff]

@[simp]
lemma nonnegative_singleAt (k : ℕ) : Nonnegative (singleAt (n := n) k) := by
  intro i
  unfold singleAt
  split_ifs <;> norm_num

lemma size_singleAt {k : ℕ} (bound : k < 3 * n) : size (singleAt (n := n) k) = 1 := by
  rw [show singleAt k = single (⟨k, bound⟩ : Rank n) from
    singleAt_eq_single (⟨k, bound⟩ : Rank n)]
  exact size_single _

lemma rankSum_singleAt {k : ℕ} (bound : k < 3 * n) :
    rankSum (singleAt (n := n) k) = (k : ℤ) + 1 := by
  rw [show singleAt k = single (⟨k, bound⟩ : Rank n) from
    singleAt_eq_single (⟨k, bound⟩ : Rank n), rankSum_single]
  rfl

lemma reverse_singleAt {k : ℕ} (bound : k < 3 * n) :
    reverse (singleAt (n := n) k) = singleAt (3 * n - 1 - k) := by
  ext i
  have := i.isLt
  simp only [reverse_apply, singleAt_apply, Fin.val_rev]
  split_ifs <;> omega

/-- One tile at every zero-based index in `[a,b)`. -/
def segment (a b : ℕ) : VirtualHand n := fun i ↦ if a ≤ i.val ∧ i.val < b then 1 else 0

@[grind =]
lemma segment_apply (a b : ℕ) (i : Rank n) :
    segment a b i = if a ≤ i.val ∧ i.val < b then 1 else 0 := rfl

@[simp]
lemma nonnegative_segment (a b : ℕ) : Nonnegative (segment (n := n) a b) := by
  intro i
  unfold segment
  split_ifs <;> norm_num

lemma size_segment {a b : ℕ} (bound : b ≤ 3 * n) :
    size (segment (n := n) a b) = (b - a : ℕ) := by
  change (∑ i : Fin (3 * n), if a ≤ i.val ∧ i.val < b then (1 : ℤ) else 0) = _
  change (∑ i : Fin (3 * n), (fun k : ℕ ↦ if a ≤ k ∧ k < b then (1 : ℤ) else 0) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ if a ≤ k ∧ k < b then (1 : ℤ) else 0),
    ← Finset.sum_filter]
  have indices : (Finset.range (3 * n)).filter (fun i ↦ a ≤ i ∧ i < b) = Finset.Ico a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  simp [indices]

lemma segment_split {a b : ℕ} (i : Rank n) (lower : a ≤ i.val) (upper : i.val < b) :
    segment a b - single i = segment a i.val + segment (i.val + 1) b := by
  ext j
  simp only [Pi.sub_apply, Pi.add_apply, segment_apply, single_apply, Fin.ext_iff]
  split_ifs <;> omega

lemma interiorOnes_eq_segment : (interiorOnes : VirtualHand n) = segment 1 (3 * n - 1) := by
  ext i
  have bound := i.isLt
  simp only [interiorOnes_apply, segment_apply]
  split_ifs <;> omega

end Mahjong.VirtualHand
