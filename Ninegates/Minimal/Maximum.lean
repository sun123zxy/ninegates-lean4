/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.One
public import Ninegates.Minimal.Upper
public import Ninegates.Classification
public import Mathlib.Order.Lattice.Nat

/-! The maximum permitted meld count of a minimal full wait exists at every
positive order. Its exact general value is not assumed. -/

@[expose] public section

namespace Mahjong.VirtualHand

def minimalMeldCounts (n : ℕ) : Set ℕ := {m | ∃ c : VirtualHand n, IsMinimalFullWait m c}

noncomputable def maxMinimalMeldCount (n : ℕ) : ℕ := sSup (minimalMeldCounts n)

lemma minimalMeldCounts_bddAbove (n : ℕ) : BddAbove (minimalMeldCounts n) := by
  refine ⟨8 * n, ?_⟩
  rintro m ⟨c, minimal⟩
  exact le_of_lt minimal.meldCount_lt_eight_order

lemma minimalMeldCounts_nonempty {n : ℕ} (positive : 0 < n) : (minimalMeldCounts n).Nonempty := by
  by_cases order : 2 ≤ n
  · exact ⟨n + 1, Standard.A n, (Standard.A_full order).minimal_succ⟩
  · have one : n = 1 := by omega
    subst n
    exact ⟨2, Standard.One 0, (Standard.One_live 0).1.minimal_succ⟩

lemma exists_minimal_at_max {n : ℕ} (positive : 0 < n) :
    ∃ c : VirtualHand n, IsMinimalFullWait (maxMinimalMeldCount n) c :=
  Nat.sSup_mem (minimalMeldCounts_nonempty positive) (minimalMeldCounts_bddAbove n)

lemma IsMinimalFullWait.le_max {n m : ℕ} {c : VirtualHand n} (minimal : IsMinimalFullWait m c) :
    m ≤ maxMinimalMeldCount n := le_csSup (minimalMeldCounts_bddAbove n) ⟨c, minimal⟩

lemma maxMinimalMeldCount_gt_order {n : ℕ} (positive : 0 < n) : n < maxMinimalMeldCount n := by
  obtain ⟨c, minimal⟩ := exists_minimal_at_max positive
  exact minimal.meldCount_gt_order

lemma maxMinimalMeldCount_lt_eight_order {n : ℕ} (positive : 0 < n) :
    maxMinimalMeldCount n < 8 * n := by
  obtain ⟨c, minimal⟩ := exists_minimal_at_max positive
  exact minimal.meldCount_lt_eight_order

@[simp]
lemma maxMinimalMeldCount_one : maxMinimalMeldCount 1 = 2 := by
  obtain ⟨c, minimal⟩ := exists_minimal_at_max (n := 1) (by decide)
  exact (orderOne_isMinimalFullWait_iff.mp minimal).1

end Mahjong.VirtualHand
