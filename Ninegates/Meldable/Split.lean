/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Cut
public import Ninegates.Meldable.Reverse
public import Ninegates.Meldable.Triplets

/-! A missing rank separates actual meld placements. Nonnegativity rules out
every sequence crossing the cut, without a canonical-placement assumption. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

namespace Placement

lemma Nonnegative.coefficients_of_zero {p : Placement n} (h : p.Nonnegative)
    (k : Rank n) (missing : p.toHand k = 0) :
    coefficient p.seqNum k.val = 0 ∧ coefficient p.seqNum ((k.val : ℤ) - 1) = 0 ∧
      coefficient p.seqNum ((k.val : ℤ) - 2) = 0 ∧ p.tripNum k = 0 := by
  have current := coefficient_nonnegative h.1 (k.val : ℤ)
  have previous := coefficient_nonnegative h.1 ((k.val : ℤ) - 1)
  have older := coefficient_nonnegative h.1 ((k.val : ℤ) - 2)
  have triplet : 0 ≤ p.tripNum k := h.2 k
  rw [toHand_apply] at missing
  omega

def leftOf (p : Placement n) (k : Rank n) : Placement n where
  seqNum j := if j.val < k.val then p.seqNum j else 0
  tripNum i := if i.val < k.val then p.tripNum i else 0

lemma Nonnegative.leftOf {p : Placement n} (h : p.Nonnegative) (k : Rank n) :
    (p.leftOf k).Nonnegative := by
  constructor <;> intro i <;> dsimp [Placement.leftOf] <;> split_ifs
  · exact h.1 i
  · norm_num
  · exact h.2 i
  · norm_num

lemma Nonnegative.toHand_leftOf {p : Placement n} (h : p.Nonnegative) (k : Rank n)
    (missing : p.toHand k = 0) : (p.leftOf k).toHand = VirtualHand.leftOf k p.toHand := by
  obtain ⟨_, previous, older, _⟩ := h.coefficients_of_zero k missing
  have stopped (t : ℤ) (lower : (k.val : ℤ) - 2 ≤ t) :
      coefficient (p.leftOf k).seqNum t = 0 := by
    rw [Placement.leftOf, coefficient_restrict_lt]
    split_ifs with before
    · have boundary : t = (k.val : ℤ) - 1 ∨ t = (k.val : ℤ) - 2 := by omega
      rcases boundary with rfl | rfl <;> assumption
    · rfl
  ext i
  by_cases before : i.val < k.val
  · simp only [toHand_apply, Placement.leftOf, coefficient_restrict_lt, VirtualHand.leftOf_apply]
    have current : (i.val : ℤ) < k.val := by omega
    have previous : (i.val : ℤ) - 1 < k.val := by omega
    have older : (i.val : ℤ) - 2 < k.val := by omega
    simp only [ite_eq_left before, ite_eq_left current, ite_eq_left previous, ite_eq_left older]
  · simp only [toHand_apply, VirtualHand.leftOf_apply, ite_eq_right before]
    rw [stopped i.val (by omega), stopped ((i.val : ℤ) - 1) (by omega),
      stopped ((i.val : ℤ) - 2) (by omega)]
    simp only [Placement.leftOf, ite_eq_right before, mul_zero, add_zero]

end Placement

lemma Meldable.leftOf {c : VirtualHand n} (h : Meldable c) (k : Rank n) (missing : c k = 0) :
    Meldable (VirtualHand.leftOf k c) := by
  obtain ⟨p, positive, rfl⟩ := h
  exact ⟨p.leftOf k, positive.leftOf k, positive.toHand_leftOf k missing⟩

lemma Meldable.rightOf {c : VirtualHand n} (h : Meldable c) (k : Rank n) (missing : c k = 0) :
    Meldable (VirtualHand.rightOf k c) := by
  have reflected := h.reverse.leftOf k.rev (by simpa using missing)
  rw [leftOf_reverse] at reflected
  simpa using reflected.reverse

/-- `prp-meldable-split`: a missing rank separates the two actual remainders. -/
lemma meldable_split {c : VirtualHand n} (k : Rank n) (missing : c k = 0) :
    Meldable c ↔ Meldable (leftOf k c) ∧ Meldable (rightOf k c) := by
  constructor
  · intro h
    exact ⟨h.leftOf k missing, h.rightOf k missing⟩
  · rintro ⟨left, right⟩
    have combined := left.add right
    rwa [leftOf_add_rightOf c k missing] at combined

end Mahjong.VirtualHand
