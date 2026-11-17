/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Defs
public import Ninegates.Meldable.Defs
public import Ninegates.Wait.Defs
public import Ninegates.Minimal.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite

/-! Trusted statement model for arXiv:2611.06944v1 (2026-11-02).
The shared project imports above contain only foundational definitions.
Derived objects are independently defined below, without importing any project
proof modules. The solution must bridge this model to the implemented library.
There are no assumptions about any paper result and no theorem holes here. -/

@[expose] public section

namespace ComparatorChallenges.Spec

open Mahjong Mahjong.VirtualHand

variable {n : ℕ}

def singleAt (k : ℕ) : VirtualHand n := fun i ↦ if i.val = k then 1 else 0

def segment (a b : ℕ) : VirtualHand n := fun i ↦ if a ≤ i.val ∧ i.val < b then 1 else 0

def interiorOnes : VirtualHand n := fun i ↦ if 0 < i.val ∧ i.val + 1 < 3 * n then 1 else 0

def leftOf (k : Rank n) : VirtualHand n →ₗ[ℤ] VirtualHand n where
  toFun c i := if i.val < k.val then c i else 0
  map_add' _ _ := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' _ _ := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

def rightOf (k : Rank n) : VirtualHand n →ₗ[ℤ] VirtualHand n where
  toFun c i := if k.val < i.val then c i else 0
  map_add' _ _ := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' _ _ := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

section
variable {N : ℕ} {R : Type*} [Zero R]

def coefficient (s : Fin N → R) (k : ℤ) : R :=
  if h : 0 ≤ k ∧ k < N then s ⟨k.toNat, by omega⟩ else 0

end

def sequenceHand : (Fin (3 * n - 2) → ℤ) →ₗ[ℤ] VirtualHand n where
  toFun s := ∑ j, s j • sequence j
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum, mul_assoc]

def VirtuallySequential (c : VirtualHand n) : Prop := ∃ s, sequenceHand s = c

def Sequential (c : VirtualHand n) : Prop := ∃ s, 0 ≤ s ∧ sequenceHand s = c

namespace Placement

def sequenceCount (p : Placement n) : ℤ := ∑ j, p.seqNum j

def Canonic (p : Placement n) : Prop := ∀ j, 0 ≤ p.seqNum j ∧ p.seqNum j < 3

def canonicalize (p : Placement n) : Placement n where
  seqNum j := p.seqNum j % 3
  tripNum i := p.tripNum i + coefficient (fun j ↦ p.seqNum j / 3) i.val +
    coefficient (fun j ↦ p.seqNum j / 3) ((i.val : ℤ) - 1) +
    coefficient (fun j ↦ p.seqNum j / 3) ((i.val : ℤ) - 2)

end Placement

namespace SequenceScan

variable {R : Type*} [AddCommGroup R]

def run (a : ℕ → R) : ℕ → R × R
  | 0 => (0, 0)
  | k + 1 =>
      let previous := run a k
      (a k - previous.1 - previous.2, previous.1)

end SequenceScan

def sequenceScan (c : VirtualHand n) : ℕ → ℤ × ℤ :=
  SequenceScan.run fun k ↦ coefficient c (k : ℤ)

def recoveredSequences (c : VirtualHand n) : Fin (3 * n - 2) → ℤ :=
  fun j ↦ (sequenceScan c (j.val + 1)).1

def canonicalSequence (c : VirtualHand n) (j : ℕ) : ℤ := (sequenceScan c j).1 % 3

def canonicalTriplet (c : VirtualHand n) (i : Rank n) : ℤ :=
  (c i - canonicalSequence c (i.val + 1) - canonicalSequence c i.val -
    canonicalSequence c (i.val - 1)) / 3

def scanPlacement (c : VirtualHand n) : Placement n where
  seqNum j := canonicalSequence c (j.val + 1)
  tripNum i := canonicalTriplet c i

def moveTile (c : VirtualHand n) (i j : Rank n) : VirtualHand n := c - single i + single j

namespace Moving

abbrev Start (n : ℕ) := Fin (3 * n - 3)

def rankAt (r : Start n) (d : Fin 4) : Rank n := ⟨r.val + d.val, by omega⟩

def sequenceAt (r : Start n) (d : Fin 2) : Fin (3 * n - 2) :=
  ⟨r.val + d.val, by omega⟩

def right (c : VirtualHand n) (r : Start n) : VirtualHand n :=
  c - single (rankAt r 0) + single (rankAt r 3)

def shift (s : Fin (3 * n - 2) → ℤ) (r : Start n) : Fin (3 * n - 2) → ℤ :=
  s - Pi.single (sequenceAt r 0) 1 + Pi.single (sequenceAt r 1) 1

def step (p : Placement n) (r : Start n) : Placement n where
  seqNum := shift p.seqNum r
  tripNum := p.tripNum

def borrow (p : Placement n) (r : Start n) : ℤ :=
  if p.seqNum (sequenceAt r 0) = 0 then 1 else 0

def carry (p : Placement n) (r : Start n) : ℤ :=
  if p.seqNum (sequenceAt r 1) = 2 then 1 else 0

def delta (a b k : ℤ) : ℤ :=
  if a ≤ k ∧ k < b then
    if (k - a) % 3 = 0 then -1 else if (k - a) % 3 = 1 then 1 else 0
  else 0

def shiftAlong (s : Fin (3 * n - 2) → ℤ) (i j : Rank n) : Fin (3 * n - 2) → ℤ :=
  s + fun r ↦ delta i.val j.val r.val

def shiftAlongLeft (s : Fin (3 * n - 2) → ℤ) (i j : Rank n) : Fin (3 * n - 2) → ℤ :=
  s - fun r ↦ delta j.val i.val r.val

end Moving

def Pillar (c : VirtualHand n) (p : Rank n) : Prop :=
  3 ≤ c p ∧ ∀ a : Rank n, rankClass a = rankClass p → 2 ≤ c a → a = p

def fixedClass (c : VirtualHand n) : ZMod 3 := (rankSum c : ZMod 3)

def pairedClass (c : VirtualHand n) (r : ZMod 3) : ZMod 3 := -fixedClass c - r

def TwoPair (c : VirtualHand n) (p q : Rank n) : Prop :=
  p ≠ q ∧ Meldable (c - pair p - pair q)

namespace Standard

def A (n : ℕ) : VirtualHand n :=
  interiorOnes + (3 : ℤ) • singleAt 0 + (3 : ℤ) • singleAt (3 * n - 1)

def B (n : ℕ) : VirtualHand n :=
  interiorOnes + (3 : ℤ) • singleAt 0 + (3 : ℤ) • singleAt (3 * n - 4)

def C (n : ℕ) : VirtualHand n :=
  segment 0 (3 * n - 2) + (3 : ℤ) • singleAt 2 + (3 : ℤ) • singleAt (3 * n - 2)

def D (n : ℕ) : VirtualHand n :=
  segment 3 (3 * n - 2) + segment 1 4 +
    (3 : ℤ) • singleAt 2 + (3 : ℤ) • singleAt (3 * n - 2)

def E (n : ℕ) : VirtualHand n :=
  interiorOnes + (3 : ℤ) • singleAt 3 + (3 : ℤ) • singleAt (3 * n - 4)

def B' (n : ℕ) : VirtualHand n := reverse (B n)
def C' (n : ℕ) : VirtualHand n := reverse (C n)
def D' (n : ℕ) : VirtualHand n := reverse (D n)

def Eight (n : ℕ) : Fin 8 → VirtualHand n :=
  ![A n, B n, B' n, C n, C' n, D n, D' n, E n]

def EightFamily {n : ℕ} (c : VirtualHand n) : Prop :=
  c = A n ∨ c = B n ∨ c = B' n ∨ c = C n ∨ c = C' n ∨ c = D n ∨ c = D' n ∨ c = E n

end Standard

namespace Standard

def One : Fin 6 → VirtualHand 1 :=
  ![![3, 1, 3], ![2, 3, 2], ![3, 3, 1], ![1, 3, 3], ![3, 2, 2], ![2, 2, 3]]

def OrderOneFamily (c : VirtualHand 1) : Prop := ∃ k, c = One k

end Standard

def minimalMeldCounts (n : ℕ) : Set ℕ := {m | ∃ c : VirtualHand n, IsMinimalFullWait m c}

noncomputable def maxMinimalMeldCount (n : ℕ) : ℕ := sSup (minimalMeldCounts n)

def abundanceThreshold : VirtualHand n := fun i ↦
  if i.val = 0 ∨ i.val + 1 = 3 * n then 2
  else if i.val = 1 ∨ i.val + 2 = 3 * n then 4 else 6

namespace AlternatingWait

def hand (n : ℕ) : VirtualHand n := fun i ↦
  if i.val = 0 then 2 else if i.val = 1 then 4 else if i.val = 2 then 6
  else if i.val = 3 then 3 else if 3 * n - 2 ≤ i.val then 2
  else if n % 2 = 1 ∧ i.val = 4 then 3 else if (i.val + n) % 2 = 0 then 5 else 4

def even (a : ℕ) : VirtualHand (2 * a + 2) := hand (2 * a + 2)

def odd (a : ℕ) : VirtualHand (2 * a + 3) := hand (2 * a + 3)

def meldCount (n : ℕ) : ℕ := 9 * n / 2 - 3

end AlternatingWait

namespace ClassBoundSharpness

def hand (n : ℕ) : VirtualHand n :=
  interiorOnes + (2 : ℤ) • segment 1 4 + (3 : ℤ) • singleAt (3 * n - 1)

end ClassBoundSharpness

namespace Examples

def largeHand : VirtualHand 2 := ![0, 2, 2, 4, 2, 3]

def fixedNoLoop : VirtualHand 3 := ![2, 2, 2, 3, 3, 2, 4, 1, 3]

def orderOneMiddleTriple : VirtualHand 1 := ![2, 3, 2]

end Examples

end ComparatorChallenges.Spec
