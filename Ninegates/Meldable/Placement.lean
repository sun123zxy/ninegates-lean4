/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Statistics

/-! Combining actual placements and bounding their individual meld counts. -/

@[expose] public section

namespace Mahjong.VirtualHand.Placement

variable {n : ℕ}

def add (p q : Placement n) : Placement n :=
  ⟨p.seqNum + q.seqNum, p.tripNum + q.tripNum⟩

@[simp]
lemma add_seqNum (p q : Placement n) : (p.add q).seqNum = p.seqNum + q.seqNum := rfl

@[simp]
lemma add_tripNum (p q : Placement n) : (p.add q).tripNum = p.tripNum + q.tripNum := rfl

@[simp]
lemma toHand_add (p q : Placement n) : (p.add q).toHand = p.toHand + q.toHand := by
  simp only [toHand_eq, add_seqNum, add_tripNum, map_add, smul_add]
  abel

lemma Nonnegative.add {p q : Placement n} (hp : p.Nonnegative) (hq : q.Nonnegative) :
    (p.add q).Nonnegative := ⟨add_nonneg hp.1 hq.1, add_nonneg hp.2 hq.2⟩

lemma Nonnegative.seqNum_le_last {p : Placement n} (positive : p.Nonnegative)
    (r : Fin (3 * n - 2)) : p.seqNum r ≤ p.toHand ⟨r.val + 2, by omega⟩ := by
  let i : Rank n := ⟨r.val + 2, by omega⟩
  have index : (i.val : ℤ) - 2 = r.val := by dsimp [i]; omega
  change p.seqNum r ≤ p.toHand i
  rw [toHand_apply, index, coefficient_fin]
  have current := coefficient_nonnegative positive.1 i.val
  have previous := coefficient_nonnegative positive.1 ((i.val : ℤ) - 1)
  have triplet : 0 ≤ p.tripNum i := positive.2 i
  omega

lemma Nonnegative.canonic_of_hand_le_two {p : Placement n} (positive : p.Nonnegative)
    (upper : ∀ i, p.toHand i ≤ 2) : p.Canonic := by
  intro r
  have bound := positive.seqNum_le_last r
  have two := upper ⟨r.val + 2, by omega⟩
  have lower : 0 ≤ p.seqNum r := positive.1 r
  exact ⟨lower, by omega⟩

lemma Nonnegative.tripNum_eq_zero_of_hand_le_two {p : Placement n} (positive : p.Nonnegative)
    (upper : ∀ i, p.toHand i ≤ 2) : p.tripNum = 0 := by
  ext i
  have bound := positive.triplet_le_hand i
  have two := upper i
  have lower : 0 ≤ p.tripNum i := positive.2 i
  change p.tripNum i = 0
  omega

lemma seqNum_emod_eq_canonicalSequence (p : Placement n) (r : Fin (3 * n - 2)) :
    p.seqNum r % 3 = canonicalSequence p.toHand (r.val + 1) := by
  have identity := p.canonic_canonicalize.canonicalSequence_eq (r.val + 1) (by omega)
  have index : ((r.val + 1 : ℕ) : ℤ) - 1 = r.val := by omega
  rw [toHand_canonicalize, index, coefficient_fin] at identity
  exact identity.symm

end Mahjong.VirtualHand.Placement
