/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Defs
public import Ninegates.Hand.Size
public import Ninegates.Wait.Bounds

/-! Every full wait at the least possible meld count is automatically minimal. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

lemma IsMinimalFullWait.meldCount_gt_order (minimal : IsMinimalFullWait m c) : n < m :=
  minimal.full.meldCount_gt_order

lemma IsFullWait.minimal_succ (full : IsFullWait (n + 1) c) :
    IsMinimalFullWait (n + 1) c := by
  refine ⟨full, ?_⟩
  intro k remainder removed smaller meldable equal
  have lower := smaller.meldCount_gt_order
  have positive := meldable.nonnegative.size_nonnegative
  have count := congrArg size equal
  rw [map_add, full.2.1, smaller.2.1] at count
  push_cast at count
  apply meldable.nonnegative.size_eq_zero_iff.mp
  omega

lemma isMinimalFullWait_succ_iff : IsMinimalFullWait (n + 1) c ↔ IsFullWait (n + 1) c :=
  ⟨IsMinimalFullWait.full, IsFullWait.minimal_succ⟩

end Mahjong.VirtualHand
