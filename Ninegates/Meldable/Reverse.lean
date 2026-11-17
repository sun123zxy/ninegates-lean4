/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Canonical

/-! Reversing ranks preserves sequence and meld placements, including their
canonical form. Zero extension makes the boundary cases uniform. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n N : ℕ}

lemma coefficient_reverse {R : Type*} [Zero R] (s : Fin N → R) (k : ℤ) :
    coefficient (fun j ↦ s j.rev) k = coefficient s ((N : ℤ) - 1 - k) := by
  by_cases inside : 0 ≤ k ∧ k < N
  · have reflected : 0 ≤ (N : ℤ) - 1 - k ∧ (N : ℤ) - 1 - k < N := by omega
    simp only [coefficient, dite_eq_left inside, dite_eq_left reflected]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  · have outside : ¬(0 ≤ (N : ℤ) - 1 - k ∧ (N : ℤ) - 1 - k < N) := by omega
    simp only [coefficient, dite_eq_right inside, dite_eq_right outside]

@[simp]
lemma reverse_single (i : Rank n) : reverse (single i) = single i.rev := by
  ext j
  simp only [reverse_apply, single_apply]
  have equal : j.rev = i ↔ j = i.rev := by
    constructor <;> intro h <;> simpa using congrArg Fin.rev h
  simp only [equal]

namespace Placement

def reverse (p : Placement n) : Placement n where
  seqNum j := p.seqNum j.rev
  tripNum i := p.tripNum i.rev

@[simp, grind =]
lemma reverse_seqNum (p : Placement n) (j : Fin (3 * n - 2)) :
    p.reverse.seqNum j = p.seqNum j.rev := rfl

@[simp, grind =]
lemma reverse_tripNum (p : Placement n) (i : Rank n) :
    p.reverse.tripNum i = p.tripNum i.rev := rfl

@[simp]
lemma reverse_reverse (p : Placement n) : p.reverse.reverse = p := by ext <;> simp

@[simp]
lemma toHand_reverse (p : Placement n) : p.reverse.toHand = VirtualHand.reverse p.toHand := by
  by_cases zero : n = 0
  · subst n
    ext i
    exact Fin.elim0 i
  · have length : (↑(3 * n - 2) : ℤ) = 3 * n - 2 := by omega
    ext i
    have reflected : (i.rev.val : ℤ) = 3 * n - 1 - i.val := by
      simp only [Fin.val_rev]
      omega
    simp only [toHand_apply, reverse_apply, reverse, coefficient_reverse, length, reflected]
    have first : 3 * (n : ℤ) - 2 - 1 - i.val = (3 * n - 1 - i.val) - 2 := by omega
    have second : 3 * (n : ℤ) - 2 - 1 - (i.val - 1) = (3 * n - 1 - i.val) - 1 := by omega
    have third : 3 * (n : ℤ) - 2 - 1 - (i.val - 2) = 3 * n - 1 - i.val := by omega
    rw [first, second, third]
    ring

lemma Nonnegative.reverse {p : Placement n} (h : p.Nonnegative) : p.reverse.Nonnegative :=
  ⟨fun j ↦ h.1 j.rev, fun i ↦ h.2 i.rev⟩

lemma Canonic.reverse {p : Placement n} (h : p.Canonic) : p.reverse.Canonic :=
  fun j ↦ h j.rev

@[simp]
lemma canonicalize_reverse (p : Placement n) :
    p.reverse.canonicalize = p.canonicalize.reverse := by
  apply canonic_unique (canonic_canonicalize _) (canonic_canonicalize p).reverse
  simp

end Placement

@[simp]
lemma sequenceHand_reverse (s : Fin (3 * n - 2) → ℤ) :
    sequenceHand (fun j ↦ s j.rev) = reverse (sequenceHand s) := by
  have reflected := Placement.toHand_reverse (⟨s, 0⟩ : Placement n)
  rw [Placement.toHand_no_triplets] at reflected
  change (⟨fun j ↦ s j.rev, 0⟩ : Placement n).toHand =
    reverse (sequenceHand s) at reflected
  simpa only [Placement.toHand_no_triplets] using reflected

lemma VirtuallySequential.reverse {c : VirtualHand n} (h : VirtuallySequential c) :
    VirtuallySequential (reverse c) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨fun j ↦ s j.rev, sequenceHand_reverse s⟩

lemma Sequential.reverse {c : VirtualHand n} (h : Sequential c) : Sequential (reverse c) := by
  obtain ⟨s, nonnegative, rfl⟩ := h
  exact ⟨fun j ↦ s j.rev, fun j ↦ nonnegative j.rev, sequenceHand_reverse s⟩

lemma VirtuallyMeldable.reverse {c : VirtualHand n} (h : VirtuallyMeldable c) :
    VirtuallyMeldable (reverse c) := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨p.reverse, p.toHand_reverse⟩

lemma Meldable.reverse {c : VirtualHand n} (h : Meldable c) : Meldable (reverse c) := by
  obtain ⟨p, nonnegative, rfl⟩ := h
  exact ⟨p.reverse, nonnegative.reverse, p.toHand_reverse⟩

@[simp]
lemma sequential_reverse_iff (c : VirtualHand n) : Sequential (reverse c) ↔ Sequential c :=
  ⟨fun h ↦ by simpa using h.reverse, Sequential.reverse⟩

@[simp]
lemma meldable_reverse_iff (c : VirtualHand n) : Meldable (reverse c) ↔ Meldable c :=
  ⟨fun h ↦ by simpa using h.reverse, Meldable.reverse⟩

end Mahjong.VirtualHand
