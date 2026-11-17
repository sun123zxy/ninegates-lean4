/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Necessity
public import Ninegates.Standard.WaitOne
public import Ninegates.Standard.WaitTwo
public import Ninegates.Minimal.Basic

/-! Structural classification of full-sided `(n,n+1)` waits at order `n≥2`.
No hand enumeration or computational decision procedure is used. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

lemma Standard.EightFamily.full (order : 2 ≤ n) (h : Standard.EightFamily c) :
    IsFullWait (n + 1) c := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Standard.A_full order
  · exact Standard.B_full order
  · exact (Standard.B_full order).reverse
  · exact Standard.C_full order
  · exact (Standard.C_full order).reverse
  · exact Standard.D_full order
  · exact (Standard.D_full order).reverse
  · exact Standard.E_full order

/-- The order-at-least-two part of the paper's main classification theorem. -/
lemma isFullWait_iff_eightFamily (order : 2 ≤ n) :
    IsFullWait (n + 1) c ↔ Standard.EightFamily c :=
  ⟨fun h ↦ h.eightFamily order, fun h ↦ h.full order⟩

lemma isMinimalFullWait_iff_eightFamily (order : 2 ≤ n) :
    IsMinimalFullWait (n + 1) c ↔ Standard.EightFamily c := by
  rw [isMinimalFullWait_succ_iff, isFullWait_iff_eightFamily order]

lemma Standard.A_live (order : 2 ≤ n) : IsLiveFullWait 4 (n + 1) (Standard.A n) := by
  apply isLiveFullWait_iff.mpr
  refine ⟨Standard.A_full order, ?_⟩
  intro i
  rw [Standard.A_apply]
  split_ifs <;> norm_num

private lemma not_live_of_four {m : ℕ} (i : Rank n) (four : c i = 4) :
    ¬IsLiveFullWait 4 m c := by
  intro live
  have bound := (isLiveFullWait_iff.mp live).2 i
  rw [four] at bound
  omega

lemma Standard.B_not_live (order : 2 ≤ n) : ¬IsLiveFullWait 4 (n + 1) (Standard.B n) := by
  apply not_live_of_four (⟨3 * n - 4, by omega⟩ : Rank n)
  rw [Standard.B_apply order]
  dsimp only
  split_ifs <;> omega

lemma Standard.C_not_live (order : 2 ≤ n) : ¬IsLiveFullWait 4 (n + 1) (Standard.C n) := by
  apply not_live_of_four (⟨2, by omega⟩ : Rank n)
  rw [Standard.C_apply order]
  norm_num

lemma Standard.D_not_live (order : 2 ≤ n) : ¬IsLiveFullWait 4 (n + 1) (Standard.D n) := by
  apply not_live_of_four (⟨2, by omega⟩ : Rank n)
  rw [Standard.D_apply order]
  dsimp only
  split_ifs <;> norm_num at * <;> omega

lemma Standard.E_not_live (order : 2 ≤ n) : ¬IsLiveFullWait 4 (n + 1) (Standard.E n) := by
  apply not_live_of_four (⟨3, by omega⟩ : Rank n)
  rw [Standard.E_apply order]
  dsimp only
  split_ifs <;> norm_num at * <;> omega

/-- Among full-sided waits with live draws under the four-copy bound, only
the generalized Nine Gates hand remains. -/
lemma liveFullWait_unique (order : 2 ≤ n) (live : IsLiveFullWait 4 (n + 1) c) :
    c = Standard.A n := by
  rcases live.1.eightFamily order with equal | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact equal
  · exact (Standard.B_not_live order live).elim
  · exact (Standard.B_not_live order (isLiveFullWait_reverse_iff.mp live)).elim
  · exact (Standard.C_not_live order live).elim
  · exact (Standard.C_not_live order (isLiveFullWait_reverse_iff.mp live)).elim
  · exact (Standard.D_not_live order live).elim
  · exact (Standard.D_not_live order (isLiveFullWait_reverse_iff.mp live)).elim
  · exact (Standard.E_not_live order live).elim

lemma isLiveFullWait_iff_eq_A (order : 2 ≤ n) :
    IsLiveFullWait 4 (n + 1) c ↔ c = Standard.A n := by
  refine ⟨liveFullWait_unique order, ?_⟩
  rintro rfl
  exact Standard.A_live order

end Mahjong.VirtualHand
