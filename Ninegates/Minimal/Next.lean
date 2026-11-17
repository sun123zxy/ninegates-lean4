/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Classification
public import Ninegates.Standard.Distinct
public import Ninegates.Minimal.Criterion

/-! Nonminimal waits just above the classified meld count are obtained by adding
one elementary meld to a standard family. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma next_full_not_minimal_iff {n : ℕ} (order : 2 ≤ n) (c : VirtualHand n) :
    (IsFullWait (n + 2) c ∧ ¬IsMinimalFullWait (n + 2) c) ↔
      ∃ k : Fin 8, (∃ i : Rank n, c = Standard.Eight n k + triplet i) ∨
        ∃ r : Fin (3 * n - 2), c = Standard.Eight n k + sequence r := by
  classical
  constructor
  · rintro ⟨full, nonminimal⟩
    have step : n + 2 - 1 = n + 1 := by omega
    rw [isMinimalFullWait_iff_no_elementary_removal] at nonminimal
    simp only [full, true_and, step, not_and_or, not_forall, not_not] at nonminimal
    rcases nonminimal with ⟨i, smaller⟩ | ⟨r, smaller⟩
    · obtain ⟨k, equal⟩ := (Standard.eightFamily_iff_exists (c - triplet i)).mp
        (smaller.eightFamily order)
      refine ⟨k, Or.inl ⟨i, ?_⟩⟩
      rw [← equal, sub_add_cancel]
    · obtain ⟨k, equal⟩ := (Standard.eightFamily_iff_exists (c - sequence r)).mp
        (smaller.eightFamily order)
      refine ⟨k, Or.inr ⟨r, ?_⟩⟩
      rw [← equal, sub_add_cancel]
  · rintro ⟨k, (⟨i, rfl⟩ | ⟨r, rfl⟩)⟩
    · have base := ((Standard.eightFamily_iff_exists _).mpr ⟨k, rfl⟩).full order
      refine ⟨base.add_triplet i, ?_⟩
      intro minimal
      have empty := minimal.minimal base (meldable_triplet i) rfl
      have count := congrArg size empty
      simp at count
    · have base := ((Standard.eightFamily_iff_exists _).mpr ⟨k, rfl⟩).full order
      refine ⟨base.add_sequence r, ?_⟩
      intro minimal
      have empty := minimal.minimal base (meldable_sequence r) rfl
      have count := congrArg size empty
      simp at count

namespace Standard

def nextNonminimal (n : ℕ) : Finset (VirtualHand n) :=
  ((Finset.univ : Finset (Fin 8 × Rank n)).image
    (fun p ↦ Eight n p.1 + triplet p.2)) ∪
  ((Finset.univ : Finset (Fin 8 × Fin (3 * n - 2))).image
    (fun p ↦ Eight n p.1 + sequence p.2))

lemma mem_nextNonminimal {n : ℕ} (c : VirtualHand n) : c ∈ nextNonminimal n ↔
    ∃ k : Fin 8, (∃ i : Rank n, c = Eight n k + triplet i) ∨
      ∃ r : Fin (3 * n - 2), c = Eight n k + sequence r := by
  simp only [nextNonminimal, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, eq_comm, exists_or]

end Standard

lemma next_nonminimal_iff_mem {n : ℕ} (order : 2 ≤ n) (c : VirtualHand n) :
    (IsFullWait (n + 2) c ∧ ¬IsMinimalFullWait (n + 2) c) ↔ c ∈ Standard.nextNonminimal n := by
  rw [next_full_not_minimal_iff order, Standard.mem_nextNonminimal]

end Mahjong.VirtualHand
