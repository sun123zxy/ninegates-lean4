/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Classification
public import Ninegates.Standard.One

/-! Every hand in the classification respects the four-copy bound, although
only `A` has live draws at order at least two. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma Standard.EightFamily.valid (order : 2 ≤ n) {c : VirtualHand n}
    (family : Standard.EightFamily c) : Valid c := by
  have nonnegative := (family.full order).1
  have bound_B : Valid (Standard.B n) := by
    refine ⟨(Standard.B_full order).1, ?_⟩
    intro i
    rw [Standard.B_apply order]
    split_ifs <;> norm_num
  have bound_C : Valid (Standard.C n) := by
    refine ⟨(Standard.C_full order).1, ?_⟩
    intro i
    rw [Standard.C_apply order]
    split_ifs <;> norm_num
  have bound_D : Valid (Standard.D n) := by
    refine ⟨(Standard.D_full order).1, ?_⟩
    intro i
    rw [Standard.D_apply order]
    split_ifs <;> norm_num
  rcases family with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨nonnegative, ?_⟩
    intro i
    rw [Standard.A_apply]
    split_ifs <;> norm_num
  · exact bound_B
  · exact bound_B.reverse
  · exact bound_C
  · exact bound_C.reverse
  · exact bound_D
  · exact bound_D.reverse
  · refine ⟨nonnegative, ?_⟩
    intro i
    rw [Standard.E_apply order]
    split_ifs <;> norm_num

lemma Standard.One_valid (k : Fin 6) : Valid (Standard.One k) := by
  refine ⟨(Standard.One_live k).1.1, ?_⟩
  intro i
  have bound := (isLiveFullWait_iff.mp (Standard.One_live k)).2 i
  omega

lemma IsFullWait.valid_succ {c : VirtualHand n} (full : IsFullWait (n + 1) c) : Valid c := by
  have positive := full.order_pos
  by_cases order : 2 ≤ n
  · exact (full.eightFamily order).valid order
  · have one : n = 1 := by omega
    subst n
    obtain ⟨k, rfl⟩ := full.orderOneFamily
    exact Standard.One_valid k

end Mahjong.VirtualHand
