/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Basic

/-!
# Ranks grouped by congruence class

The product coordinates are a block number and a zero-based position in that
block. Paper congruence classes `1,2,0` correspond to positions `0,1,2`.
-/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def blockEquiv (n : ℕ) : Fin n × Fin 3 ≃ Rank n :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 3))

@[simp, grind =]
lemma blockEquiv_val (b : Fin n) (r : Fin 3) : (blockEquiv n (b, r)).val = 3 * b.val + r.val := by
  change r.val + 3 * b.val = 3 * b.val + r.val
  omega

@[simp]
lemma rankClass_blockEquiv (b : Fin n) (r : Fin 3) :
    rankClass (blockEquiv n (b, r)) = (r.val : ZMod 3)+1 := by
  unfold rankClass rank
  rw [blockEquiv_val]
  push_cast
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]
  ring

lemma exists_rankClass (positive : 0 < n) (s : ZMod 3) : ∃ i : Rank n, rankClass i = s := by
  let r : Fin 3 := ⟨(s - 1).val, ZMod.val_lt _⟩
  refine ⟨blockEquiv n (⟨0, positive⟩, r), ?_⟩
  rw [rankClass_blockEquiv]
  change ((s - 1).val : ZMod 3) + 1 = s
  simp

lemma classSize_blocks (c : VirtualHand n) (r : Fin 3) :
    classSize ((r.val : ZMod 3)+1) c = ∑ b : Fin n, c (blockEquiv n (b, r)) := by
  have equal (j : Fin 3) : ((j.val : ZMod 3)+1 = (r.val : ZMod 3)+1) ↔ j = r := by
    simp [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt,
      Nat.mod_eq_of_lt r.isLt, Fin.ext_iff]
  simp only [classSize, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_filter]
  rw [← (blockEquiv n).sum_comp]
  simp only [Fintype.sum_prod_type, rankClass_blockEquiv, equal]
  simp

lemma classSize_one_blocks (c : VirtualHand n) :
    classSize 1 c = ∑ b : Fin n, c (blockEquiv n (b, 0)) := by
  simpa using classSize_blocks c 0

lemma classSize_two_blocks (c : VirtualHand n) :
    classSize 2 c = ∑ b : Fin n, c (blockEquiv n (b, 1)) := by
  simpa [show (1 : ZMod 3)+1 = 2 by decide +kernel] using classSize_blocks c 1

lemma classSize_zero_blocks (c : VirtualHand n) :
    classSize 0 c = ∑ b : Fin n, c (blockEquiv n (b, 2)) := by
  simpa [show (2 : ZMod 3)+1 = 0 by decide +kernel] using classSize_blocks c 2

@[simp]
lemma classSize_const (r : ZMod 3) (z : ℤ) : classSize r (fun _ : Rank n ↦ z) = n * z := by
  let position : Fin 3 := ⟨(r - 1).val, ZMod.val_lt _⟩
  have equal : (position.val : ZMod 3) + 1 = r := by simp [position]
  rw [← equal, classSize_blocks]
  simp

lemma classSize_mono {c d : VirtualHand n} (h : c ≤ d) (r : ZMod 3) :
    classSize r c ≤ classSize r d := by
  change (∑ i ∈ Finset.univ.filter (fun i : Rank n ↦ rankClass i = r), c i) ≤ _
  exact Finset.sum_le_sum fun i _ ↦ h i

lemma Nonnegative.classSize_nonnegative {c : VirtualHand n} (h : Nonnegative c) (r : ZMod 3) :
    0 ≤ classSize r c := by
  change 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Rank n ↦ rankClass i = r), c i
  exact Finset.sum_nonneg fun i _ ↦ h i

lemma Nonnegative.le_classSize {c : VirtualHand n} (h : Nonnegative c) (i : Rank n) :
    c i ≤ classSize (rankClass i) c := by
  change c i ≤ ∑ j ∈ Finset.univ.filter (fun j : Rank n ↦ rankClass j = rankClass i), c j
  exact Finset.single_le_sum (fun j _ ↦ h j) (by simp)

lemma Nonnegative.add_le_classSize {c : VirtualHand n} (h : Nonnegative c)
    (i j : Rank n) (different : i ≠ j) (same : rankClass j = rankClass i) :
    c i + c j ≤ classSize (rankClass i) c := by
  have subset : ({i, j} : Finset (Rank n)) ⊆
      Finset.univ.filter (fun k ↦ rankClass k = rankClass i) := by
    intro k member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> simp [same]
  have bound := Finset.sum_le_sum_of_subset_of_nonneg (f := c) subset (fun k _ _ ↦ h k)
  change c i + c j ≤ ∑ k ∈ Finset.univ.filter
    (fun k : Rank n ↦ rankClass k = rankClass i), c k
  simpa [different] using bound

private lemma univ_eq_three_classes (s x y : ZMod 3) (sx : s ≠ x) (sy : s ≠ y) (xy : x ≠ y) :
    (Finset.univ : Finset (ZMod 3)) = {s, x, y} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [sx, sy, xy]

lemma three_classes_exhaust (s x y : ZMod 3) (sx : s ≠ x) (sy : s ≠ y) (xy : x ≠ y)
    (r : ZMod 3) : r = s ∨ r = x ∨ r = y := by
  have member : r ∈ (Finset.univ : Finset (ZMod 3)) := Finset.mem_univ r
  rw [univ_eq_three_classes s x y sx sy xy] at member
  simpa only [Finset.mem_insert, Finset.mem_singleton] using member

lemma size_eq_three_classSizes (c : VirtualHand n) (s x y : ZMod 3)
    (sx : s ≠ x) (sy : s ≠ y) (xy : x ≠ y) :
    size c = classSize s c + classSize x c + classSize y c := by
  rw [size_eq_sum_classSize, univ_eq_three_classes s x y sx sy xy]
  simp [sx, sy, xy, add_assoc]

lemma classSize_eq_zero {c : VirtualHand n} (r : ZMod 3)
    (zero : ∀ i, rankClass i = r → c i = 0) : classSize r c = 0 := by
  change (∑ i ∈ Finset.univ.filter (fun i : Rank n ↦ rankClass i = r), c i) = 0
  exact Finset.sum_eq_zero fun i member ↦ zero i (Finset.mem_filter.mp member).2

lemma classSize_eq_single {c : VirtualHand n} (p : Rank n)
    (others : ∀ i, rankClass i = rankClass p → i ≠ p → c i = 0) :
    classSize (rankClass p) c = c p := by
  change (∑ i ∈ Finset.univ.filter (fun i : Rank n ↦ rankClass i = rankClass p), c i) = c p
  apply Finset.sum_eq_single p
  · intro i member different
    exact others i (Finset.mem_filter.mp member).2 different
  · simp

end Mahjong.VirtualHand
