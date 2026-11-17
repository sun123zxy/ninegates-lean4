/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Defs

/-!
# Winning, waiting, and the draw-pair relation

The meld count `m` and the copy bound `cap` are separate parameters. Explicit
size and nonnegativity conditions also rule out vacuous zero-rank full waits.
Integer subtraction needs no truncated-subtraction side conditions: `Meldable`
already guarantees that the remaining hand is nonnegative.
-/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def Winning (m : ℕ) (c : VirtualHand n) : Prop :=
  size c = 3 * (m : ℤ) + 2 ∧ ∃ j, Meldable (c - pair j)

def DrawPair (c : VirtualHand n) (i j : Rank n) : Prop :=
  Meldable (c + single i - pair j)

def IsWaitingTile (m : ℕ) (c : VirtualHand n) (i : Rank n) : Prop := Winning m (c + single i)

def IsLiveWaitingTile (cap m : ℕ) (c : VirtualHand n) (i : Rank n) : Prop :=
  IsWaitingTile m c i ∧ Bounded cap (c + single i)

def IsWait (m : ℕ) (c : VirtualHand n) : Prop := Nonnegative c ∧ ∃ i, IsWaitingTile m c i

def IsFullWait (m : ℕ) (c : VirtualHand n) : Prop :=
  Nonnegative c ∧ size c = 3 * (m : ℤ) + 1 ∧ ∀ i, IsWaitingTile m c i

def IsLiveFullWait (cap m : ℕ) (c : VirtualHand n) : Prop :=
  IsFullWait m c ∧ ∀ i, Bounded cap (c + single i)

end Mahjong.VirtualHand
