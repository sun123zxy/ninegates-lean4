/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.OrderOne
public import Ninegates.Meldable.OrderOne
public import Ninegates.Wait.Bounds

/-! At order one, the class-size lower bounds completely characterize full
waits. Adding a class-dependent five-tile threshold gives a bijection with
nonnegative vectors of the corresponding smaller size. -/

@[expose] public section

namespace Mahjong.VirtualHand.OrderOne

lemma drawPair_of_threshold {c : VirtualHand 1} (count : (size c : ZMod 3) = 1)
    (large : pairThreshold (fixedClass c) ≤ c) (i j : Rank 1)
    (congruent : rankClass i + rankClass j = -(rankSum c : ZMod 3)) : DrawPair c i j := by
  have positive (k : Rank 1) : 1 ≤ c k := (pairThreshold_bounds _ k).1.trans (large k)
  have class_j : rankClass j = pairedClass c (rankClass i) := by
    unfold pairedClass fixedClass
    linear_combination congruent
  apply ((virtuallyMeldable_draw_iff count i j).mpr congruent).meldable_orderOne
  intro k
  change 0 ≤ c k + single i k - pair j k
  by_cases same : i = j
  · subst j
    have bound := positive k
    simp only [pair_apply, single_apply]
    split_ifs <;> omega
  · have nonfixed : rankClass j ≠ fixedClass c := by
      intro fixed_j
      have fixed_i := (pairedClass_eq_fixed_iff c (rankClass i)).mp
        (class_j.symm.trans fixed_j)
      exact same (rankClass_orderOne_injective (fixed_i.trans fixed_j.symm))
    by_cases target : k = j
    · subst k
      have bound := large j
      simp only [pairThreshold, ite_eq_right nonfixed] at bound
      simp only [pair_apply, single_apply, ite_eq_right (Ne.symm same), ite_true]
      omega
    · have bound := positive k
      simp only [pair_apply, single_apply, ite_eq_right target]
      split_ifs <;> omega

lemma full_iff {m : ℕ} (c : VirtualHand 1) :
    IsFullWait m c ↔ size c = 3 * (m : ℤ) + 1 ∧ pairThreshold (fixedClass c) ≤ c := by
  constructor
  · intro full
    refine ⟨full.2.1, ?_⟩
    intro i
    change (if rankClass i = fixedClass c then 1 else 2) ≤ c i
    split_ifs with fixed
    · have bound := full.fixed_class_size
      rw [← fixed, classSize_orderOne] at bound
      exact bound
    · have bound := full.nonfixed_class_size (rankClass i) fixed
      rw [classSize_orderOne] at bound
      exact bound
  · rintro ⟨count, large⟩
    apply isFullWait_iff.mpr
    refine ⟨?_, count, ?_⟩
    · intro i
      have bound := (pairThreshold_bounds _ i).1.trans (large i)
      change 0 ≤ c i
      omega
    · intro i
      obtain ⟨j, class_j⟩ := exists_rankClass (n := 1) (by decide +kernel)
        (pairedClass c (rankClass i))
      refine ⟨j, drawPair_of_threshold (size_cast_of_wait_size count) large i j ?_⟩
      rw [class_j]
      unfold pairedClass fixedClass
      ring

private lemma double_class (s : ZMod 3) : s + s = -s := by
  have three : (3 : ZMod 3) * s = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  linear_combination three

lemma fixedClass_add_threshold (c : VirtualHand 1) :
    fixedClass (c + pairThreshold (-fixedClass c)) = -fixedClass c := by
  simp only [fixedClass, map_add, Int.cast_add, rankSum_pairThreshold, neg_neg]
  exact double_class _

lemma fixedClass_sub_threshold (c : VirtualHand 1) :
    fixedClass (c - pairThreshold (fixedClass c)) = -fixedClass c := by
  simp only [fixedClass, map_sub, Int.cast_sub, rankSum_pairThreshold, sub_neg_eq_add]
  exact double_class _

/-- The class-dependent translation and its inverse on integer vectors. -/
def thresholdEquiv : VirtualHand 1 ≃ VirtualHand 1 where
  toFun c := c + pairThreshold (-fixedClass c)
  invFun c := c - pairThreshold (fixedClass c)
  left_inv c := by
    dsimp only
    rw [fixedClass_add_threshold, add_sub_cancel_right]
  right_inv c := by
    dsimp only
    rw [fixedClass_sub_threshold, neg_neg, sub_add_cancel]

lemma size_thresholdEquiv (c : VirtualHand 1) : size (thresholdEquiv c) = size c + 5 := by
  exact (map_add size c _).trans (by rw [size_pairThreshold])

lemma full_thresholdEquiv_iff {m : ℕ} (c : VirtualHand 1) :
    IsFullWait m (thresholdEquiv c) ↔ Nonnegative c ∧ size c = 3 * (m : ℤ) - 4 := by
  rw [full_iff, size_thresholdEquiv]
  change size c + 5 = _ ∧ pairThreshold (fixedClass (c + pairThreshold (-fixedClass c))) ≤
    c + pairThreshold (-fixedClass c) ↔ _
  rw [fixedClass_add_threshold, le_add_iff_nonneg_left]
  change size c + 5 = _ ∧ Nonnegative c ↔ _
  constructor
  · rintro ⟨count, positive⟩
    exact ⟨positive, by omega⟩
  · rintro ⟨positive, count⟩
    exact ⟨by omega, positive⟩

def fullWaitEquiv {m : ℕ} (order : 2 ≤ m) :
    {q : Rank 1 → ℕ // ∑ i, q i = 3 * m - 4} ≃
      {c : VirtualHand 1 // IsFullWait m c} :=
  (naturalHandEquiv (3 * m - 4)).trans
    (thresholdEquiv.subtypeEquiv (by
      intro c
      rw [full_thresholdEquiv_iff]
      have size_cast : ((3 * m - 4 : ℕ) : ℤ) = 3 * (m : ℤ) - 4 := by omega
      rw [size_cast]))

end Mahjong.VirtualHand.OrderOne
