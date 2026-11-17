/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Segment
public import Ninegates.Hand.Interior

/-! The paper's eight standard families. The interval descriptions handle the
overlapping end patterns of `E 2` uniformly. At order one, `A` is `(3,1,3)`. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

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

end Mahjong.VirtualHand.Standard
