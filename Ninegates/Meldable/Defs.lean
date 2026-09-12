/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Defs

/-!
# Meld decompositions

## Main definitions

- `Placement n` records triplet and sequence multiplicities on the finite tile
  coordinates. Sequence multiplicities at the final two coordinates are required
  to be zero.

- For a placement `p`, `p.toHand` is the hand given by the finite sum of the
  triplets and sequences specified by `p`.

- A placement is a witness for a hand when its `toHand` is that hand. A hand is
  `Meldable` when it has such a witness.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

namespace Meldable

@[ext]
structure Placement (n : ℕ) where
  tripNum : Fin (3 * n) → ℕ
  seqNum : Fin (3 * n) → ℕ
  seqNum_tail :
    (∀ i, i.val + 2 = 3 * n → seqNum i = 0) ∧
    (∀ i, i.val + 1 = 3 * n → seqNum i = 0)
deriving Repr

attribute [grind ext] Placement.ext

namespace Placement

instance : Zero (Placement n) :=
  ⟨⟨0, 0, by simp⟩⟩

instance : Add (Placement n) :=
  ⟨fun p q ↦ ⟨p.tripNum + q.tripNum, p.seqNum + q.seqNum, by
    constructor
    · intro i hi
      simp [p.seqNum_tail.1 i hi, q.seqNum_tail.1 i hi]
    · intro i hi
      simp [p.seqNum_tail.2 i hi, q.seqNum_tail.2 i hi]⟩⟩

instance : SMul ℕ (Placement n) :=
  ⟨fun k p ↦ ⟨k • p.tripNum, k • p.seqNum, by
    constructor
    · intro i hi
      simp [p.seqNum_tail.1 i hi]
    · intro i hi
      simp [p.seqNum_tail.2 i hi]⟩⟩

@[simp, grind =]
lemma tripNum_zero (i : Fin (3 * n)) : (0 : Placement n).tripNum i = 0 := rfl

@[simp, grind =]
lemma seqNum_zero (i : Fin (3 * n)) : (0 : Placement n).seqNum i = 0 := rfl

@[simp, grind =]
lemma tripNum_add (p q : Placement n) (i : Fin (3 * n)) :
    (p + q).tripNum i = p.tripNum i + q.tripNum i := rfl

@[simp, grind =]
lemma seqNum_add (p q : Placement n) (i : Fin (3 * n)) :
    (p + q).seqNum i = p.seqNum i + q.seqNum i := rfl

@[simp, grind =]
lemma tripNum_nsmul (k : ℕ) (p : Placement n) (i : Fin (3 * n)) :
    (k • p).tripNum i = k * p.tripNum i := rfl

@[simp, grind =]
lemma seqNum_nsmul (k : ℕ) (p : Placement n) (i : Fin (3 * n)) :
    (k • p).seqNum i = k * p.seqNum i := rfl

instance : AddCommMonoid (Placement n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc p q r := by ext i <;> simp [add_assoc]
  zero_add p := by ext i <;> simp
  add_zero p := by ext i <;> simp
  add_comm p q := by ext i <;> simp [add_comm]
  nsmul_zero k := by ext i <;> simp
  nsmul_succ k p := by ext i <;> simp [Nat.succ_mul, add_comm]

def toHand : Placement n →+ Hand n where
  toFun p :=
    ∑ i, p.tripNum i • Hand.triplet i +
      ∑ j, p.seqNum ⟨j.val, by omega⟩ • Hand.sequence j
  map_zero' := by simp
  map_add' _ _ := by simp [add_nsmul, Finset.sum_add_distrib]; ac_rfl

end Placement

@[grind =]
def IsWitness (p : Placement n) (c : Hand n) : Prop := p.toHand = c

end Meldable

def Meldable (c : Hand n) : Prop := ∃ p : Meldable.Placement n, Meldable.IsWitness p c

end Mahjong.Hand
