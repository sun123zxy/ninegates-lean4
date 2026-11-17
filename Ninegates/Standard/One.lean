/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.OneDefs
public import Ninegates.Wait.ClassSizes

/-! The six order-one hands. Necessity follows from the two class-size
alternatives, since every congruence class has just one rank. -/

@[expose] public section

namespace Mahjong.VirtualHand

namespace Standard

private def onePairs : Fin 6 → Rank 1 → Rank 1 :=
  ![![2, 1, 0], ![2, 1, 0], ![1, 0, 2], ![0, 2, 1], ![0, 2, 1], ![1, 0, 2]]

private lemma one_drawPair (k : Fin 6) (i : Rank 1) : DrawPair (One k) i (onePairs k i) := by
  fin_cases k <;> fin_cases i <;> rw [DrawPair, meldable_iff_tripletGreedy] <;> decide +kernel

lemma One_live (k : Fin 6) : IsLiveFullWait 4 2 (One k) := by
  apply isLiveFullWait_iff.mpr
  constructor
  · apply isFullWait_iff.mpr
    refine ⟨?_, ?_, fun i ↦ ⟨onePairs k i, one_drawPair k i⟩⟩
    · intro i
      fin_cases k <;> fin_cases i <;> norm_num [One]
    · fin_cases k <;> norm_num [One, size, Fin.sum_univ_succ]
  · intro i
    fin_cases k <;> fin_cases i <;> norm_num [One]

end Standard

private lemma classSizes_orderOne (c : VirtualHand 1) :
    classSize 0 c = c 2 ∧ classSize 1 c = c 0 ∧ classSize 2 c = c 1 := by
  have three : (3 : ZMod 3) = 0 := by decide +kernel
  have zero_two : (0 : ZMod 3) ≠ 2 := by decide +kernel
  have one_two : (1 : ZMod 3) ≠ 2 := by decide +kernel
  have two_zero : (2 : ZMod 3) ≠ 0 := by decide +kernel
  have two_one : (2 : ZMod 3) ≠ 1 := by decide +kernel
  norm_num [classSize, Finset.sum_filter, Fin.sum_univ_succ, rankClass, rank]
  simp_all

lemma IsFullWait.orderOneFamily {c : VirtualHand 1} (full : IsFullWait 2 c) :
    Standard.OrderOneFamily c := by
  obtain ⟨zero, one, two⟩ := classSizes_orderOne c
  have neg_one : (-1 : ZMod 3) = 2 := by decide +kernel
  have neg_two : (-2 : ZMod 3) = 1 := by decide +kernel
  have neg_three : (-3 : ZMod 3) = 0 := by decide +kernel
  have classes : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide +kernel
  rcases classes (fixedClass c) with fixed | fixed | fixed
  · have alternatives := full.class_sizes_alternatives 1 (by rw [fixed]; decide)
    norm_num [pairedClass, fixed, neg_one, zero, one, two] at alternatives
    rcases alternatives with ⟨c2, c0, c1⟩ | ⟨c2, c0, c1⟩
    · refine ⟨2, ?_⟩
      ext i
      fin_cases i <;> simp_all [Standard.One]
    · refine ⟨5, ?_⟩
      ext i
      fin_cases i <;> simp_all [Standard.One]
  · have alternatives := full.class_sizes_alternatives 2 (by rw [fixed]; decide)
    norm_num [pairedClass, fixed, neg_three, zero, one, two] at alternatives
    rcases alternatives with ⟨c0, c1, c2⟩ | ⟨c0, c1, c2⟩
    · refine ⟨3, ?_⟩
      ext i
      fin_cases i <;> simp_all [Standard.One]
    · refine ⟨4, ?_⟩
      ext i
      fin_cases i <;> simp_all [Standard.One]
  · have alternatives := full.class_sizes_alternatives 0 (by rw [fixed]; decide)
    norm_num [pairedClass, fixed, neg_two, zero, one, two] at alternatives
    rcases alternatives with ⟨c1, c2, c0⟩ | ⟨c1, c2, c0⟩
    · refine ⟨0, ?_⟩
      ext i
      fin_cases i <;> simp_all [Standard.One]
    · refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp_all [Standard.One]

lemma orderOne_isFullWait_iff_isOrderOneFamily {c : VirtualHand 1} :
    IsFullWait 2 c ↔ Standard.OrderOneFamily c := by
  refine ⟨IsFullWait.orderOneFamily, ?_⟩
  rintro ⟨k, rfl⟩
  exact (Standard.One_live k).1

lemma orderOne_isLiveFullWait_iff_isOrderOneFamily {c : VirtualHand 1} :
    IsLiveFullWait 4 2 c ↔ Standard.OrderOneFamily c := by
  refine ⟨fun live ↦ live.1.orderOneFamily, ?_⟩
  rintro ⟨k, rfl⟩
  exact Standard.One_live k

end Mahjong.VirtualHand
