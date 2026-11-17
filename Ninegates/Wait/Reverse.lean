/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Reverse
public import Ninegates.Wait.Graph

/-! Full waits reverse, and their fixed class is sent to `1-s`. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma IsFullWait.reverse (h : IsFullWait m c) : IsFullWait m (VirtualHand.reverse c) := by
  rw [isFullWait_iff] at h ⊢
  refine ⟨h.1.reverse, by simpa using h.2.1, ?_⟩
  intro i
  obtain ⟨j, edge⟩ := h.2.2 i.rev
  refine ⟨j.rev, ?_⟩
  simpa using edge.reverse

@[simp]
lemma isFullWait_reverse_iff : IsFullWait m (reverse c) ↔ IsFullWait m c :=
  ⟨fun h ↦ by simpa using h.reverse, IsFullWait.reverse⟩

lemma fixedClass_reverse_of_size (count : (size c : ZMod 3) = 1) :
    fixedClass (reverse c) = 1 - fixedClass c := by
  change (rankSum (reverse c) : ZMod 3) = 1 - (rankSum c : ZMod 3)
  rw [rankSum_reverse]
  push_cast
  rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add, count, one_mul]

lemma IsFullWait.fixedClass_reverse (h : IsFullWait m c) :
    fixedClass (VirtualHand.reverse c) = 1 - fixedClass c :=
  fixedClass_reverse_of_size h.size_cast

lemma IsLiveFullWait.reverse {cap : ℕ} (h : IsLiveFullWait cap m c) :
    IsLiveFullWait cap m (VirtualHand.reverse c) := by
  rw [isLiveFullWait_iff] at h ⊢
  exact ⟨h.1.reverse, fun i ↦ h.2 i.rev⟩

@[simp]
lemma isLiveFullWait_reverse_iff {cap : ℕ} :
    IsLiveFullWait cap m (reverse c) ↔ IsLiveFullWait cap m c :=
  ⟨fun h ↦ by simpa using h.reverse, IsLiveFullWait.reverse⟩

end Mahjong.VirtualHand
