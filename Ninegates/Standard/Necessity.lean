/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Basic
public import Ninegates.Meldable.RequiredPatterns
public import Ninegates.Wait.RequiredOne
public import Ninegates.Wait.Reverse

/-! Every full-sided `(n,n+1)` wait of order at least two belongs to one of the
eight named families, by the required-row argument and reflection. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

namespace IsFullWait

lemma fixed_two_standard (order : 2 ≤ n) (full : IsFullWait (n + 1) c)
    (fixed : fixedClass c = 2) :
    c = Standard.A n ∨ c = Standard.B n ∨ c = Standard.B' n ∨ c = Standard.E n := by
  obtain ⟨p, q, pillars, class_p⟩ := full.exists_pillars_class order 1 (by rw [fixed]; decide)
  obtain ⟨left, right, equal⟩ := pillars.fixed_two_decomposition_succ order full fixed class_p
  rw [RequiredSequences.sequenceHand_union_two order p q left right] at equal
  have restored : c = interiorOnes + (3 : ℤ) • singleAt p.val + (3 : ℤ) • singleAt q.val := by
    rw [equal, singleAt_eq_single, singleAt_eq_single]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pair_apply]
    ring
  rcases left with left | left <;> rcases right with right | right
  all_goals
    rw [left, right] at restored
    simp only [Standard.A, Standard.B, Standard.E, Standard.B'_eq order]
    tauto

lemma fixed_one_standard (order : 2 ≤ n) (full : IsFullWait (n + 1) c)
    (fixed : fixedClass c = 1) : c = Standard.C n ∨ c = Standard.D n := by
  obtain ⟨p, q, pillars, class_p⟩ := full.exists_pillars_class order 0 (by rw [fixed]; decide)
  obtain ⟨left, right, r, low, equal⟩ :=
    pillars.fixed_one_decomposition_succ order full fixed class_p
  rw [RequiredSequences.sequenceHand_insert_third r low,
    sequence_eq_segment] at equal
  have choices : r.val = 0 ∨ r.val = 1 := by omega
  rcases choices with start | start
  · left
    rw [equal]
    ext i
    have bound := i.isLt
    simp only [Standard.C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pair_apply,
      single_apply, Fin.ext_iff, segment_apply, singleAt_apply]
    rw [left, right, start]
    split_ifs <;> omega
  · right
    rw [equal]
    ext i
    have bound := i.isLt
    simp only [Standard.D, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pair_apply,
      single_apply, Fin.ext_iff, segment_apply, singleAt_apply]
    rw [left, right, start]
    split_ifs <;> omega

lemma eightFamily (order : 2 ≤ n) (full : IsFullWait (n + 1) c) : Standard.EightFamily c := by
  have classes : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2 := by decide +kernel
  rcases classes (fixedClass c) with fixed | fixed | fixed
  · have reversed : fixedClass (VirtualHand.reverse c) = 1 := by
      rw [full.fixedClass_reverse, fixed]
      norm_num
    rcases full.reverse.fixed_one_standard order reversed with first | second
    · have equal : c = Standard.C' n := by
        simpa only [Standard.C', reverse_reverse] using congrArg VirtualHand.reverse first
      simp only [Standard.EightFamily]
      tauto
    · have equal : c = Standard.D' n := by
        simpa only [Standard.D', reverse_reverse] using congrArg VirtualHand.reverse second
      simp only [Standard.EightFamily]
      tauto
  · have result := full.fixed_one_standard order fixed
    simp only [Standard.EightFamily]
    tauto
  · have result := full.fixed_two_standard order fixed
    simp only [Standard.EightFamily]
    tauto

end IsFullWait
end Mahjong.VirtualHand
