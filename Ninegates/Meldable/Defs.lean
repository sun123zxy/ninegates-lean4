/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Defs

/-!
# Virtual and nonnegative meld placements

The finite sequence index already excludes starts at the final two ranks.
Virtual placements may have negative coefficients; actual meld placements
require both coefficient vectors to be nonnegative.
-/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

@[ext]
structure Placement (n : ℕ) where
  seqNum : Fin (3 * n - 2) → ℤ
  tripNum : Rank n → ℤ

namespace Placement

def Nonnegative (p : Placement n) : Prop := 0 ≤ p.seqNum ∧ 0 ≤ p.tripNum

def toHand (p : Placement n) : VirtualHand n :=
  (∑ i, p.seqNum i • sequence i) + ∑ i, p.tripNum i • triplet i

def meldCount (p : Placement n) : ℤ := (∑ i, p.seqNum i) + ∑ i, p.tripNum i

end Placement

def VirtuallyMeldable (c : VirtualHand n) : Prop := ∃ p : Placement n, p.toHand = c

def Meldable (c : VirtualHand n) : Prop :=
  ∃ p : Placement n, p.Nonnegative ∧ p.toHand = c

def MeldableWith (m : ℕ) (c : VirtualHand n) : Prop := size c = 3 * (m : ℤ) ∧ Meldable c

end Mahjong.VirtualHand
