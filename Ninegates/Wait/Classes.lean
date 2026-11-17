/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Graph

/-! The class-size congruence for hands of size one modulo three. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma virtuallyMeldable_draw_iff {c : VirtualHand n}
    (count : (size c : ZMod 3) = 1) (i j : Rank n) :
    VirtuallyMeldable (c + single i - pair j) ↔
      rankClass i + rankClass j = -(rankSum c : ZMod 3) := by
  rw [virtuallyMeldable_iff_size_rankSum]
  simp only [map_sub, map_add, size_single, size_pair, rankSum_single, rankSum_pair]
  push_cast
  rw [count]
  change (1 + 1 - 2 = (0 : ZMod 3) ∧
    (rankSum c : ZMod 3) + rankClass i - 2 * rankClass j = 0) ↔ _
  · have three : (3 : ZMod 3) * rankClass j = 0 := by
      rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
    constructor
    · rintro ⟨_, weighted⟩
      linear_combination weighted + three
    · intro congruent
      refine ⟨by norm_num, ?_⟩
      linear_combination congruent - three

/-- Equal size residues leave the fixed class as the only obstruction to
virtual meldability of a difference. -/
lemma virtuallyMeldable_sub_iff_fixedClass_eq {c d : VirtualHand n}
    (count : (size c : ZMod 3) = (size d : ZMod 3)) :
    VirtuallyMeldable (c - d) ↔ fixedClass c = fixedClass d := by
  simp [virtuallyMeldable_iff_size_rankSum, fixedClass, count, sub_eq_zero]

/-- The remark after Proposition 5.10, strengthened to any two meld counts. -/
lemma IsFullWait.virtuallyMeldable_sub_iff {m k : ℕ} {c d : VirtualHand n}
    (hc : IsFullWait m c) (hd : IsFullWait k d) :
    VirtuallyMeldable (c - d) ↔ fixedClass c = fixedClass d := by
  apply virtuallyMeldable_sub_iff_fixedClass_eq
  simp [hc.2.1, hd.2.1, show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]

/-- `prp-class-size-congruence`: every nonfixed class has one fewer tile modulo
three than the fixed class. This needs only the size congruence, not waiting. -/
lemma classSize_nonfixed_congruence {c : VirtualHand n} (count : (size c : ZMod 3) = 1)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
    (classSize r c : ZMod 3) + 1 = (classSize (fixedClass c) c : ZMod 3) := by
  have positive : 0 < n := by
    by_contra not_positive
    have zero : n = 0 := by omega
    subst n
    simp [size] at count
  obtain ⟨i, class_i⟩ := exists_rankClass positive (fixedClass c)
  have virtual : VirtuallyMeldable (c - single i) := by
    apply (virtuallyMeldable_iff_size_rankSum _).mpr
    constructor
    · simp only [map_sub, size_single, Int.cast_sub, Int.cast_one, count, sub_self]
    · simp only [map_sub, rankSum_single, Int.cast_sub]
      change fixedClass c - rankClass i = 0
      rw [class_i, sub_self]
  have same := virtual.classSize_cast_eq r (fixedClass c)
  simp only [map_sub, classSize_single, class_i, ite_eq_right nonfixed.symm] at same
  push_cast at same
  linear_combination same

end Mahjong.VirtualHand
