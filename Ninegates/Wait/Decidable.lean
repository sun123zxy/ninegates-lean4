import Ninegates.Wait.Basic
import Ninegates.Winning.Decidable

/-!
# Executable decision procedures for waits and full waits
-/

namespace Mahjong.Hand

def IsWinningTile.decide (c : Hand n) (i : Fin (3 * n)) : Bool :=
  Winning.Decidable.decide (c + single i)

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsWinningTile c i) := by
  sorry

instance (c : Hand n) : Decidable (IsWait c) := by
  sorry -- by some sort of inferInstance directly from Decidable (IsWinningTile c i)

namespace IsFullWait.Decidable

open Winning.Decidable

variable {n : ℕ}

def buildPrefix (count : Array Nat) : Array StateSet := Id.run do
  let n := count.size
  let mut pref := Array.replicate (n + 1) Bitset.empty
  pref := pref.set! 0 (Bitset.singleton State.init)
  for i in List.range n do
    pref := pref.set! (i + 1) (advanceSet count[i]! pref[i]!)
  return pref

def buildSuffix (count : Array Nat) : Array StateSet := Id.run do
  let n := count.size
  let mut suff := Array.replicate (n + 1) Bitset.empty
  suff := suff.set! n (Bitset.singleton State.final)
  for k in List.range n do
    let i := n - 1 - k
    let mut good : StateSet := Bitset.empty
    for q in State.all do
      if Bitset.nonempty (Bitset.inter (step count[i]! q) suff[i + 1]!) then
        good := Bitset.insert q good
    suff := suff.set! i good
  return suff

def waitsOn (count : Array Nat)
    (pref : Array StateSet) (suff : Array StateSet) (j : Nat) : Bool :=
  if count[j]! ≥ 4 then
    false
  else
    Bitset.nonempty (Bitset.inter (advanceSet (count[j]! + 1) pref[j]!) suff[j + 1]!)

def waitingTiles (count : Array Nat) : Array Bool := Id.run do
  let n := count.size
  let pref := buildPrefix count
  let suff := buildSuffix count
  let mut result := Array.replicate n false
  for j in List.range n do
    result := result.set! j (waitsOn count pref suff j)
  return result

def waitsOnEveryTile (count : Array Nat) : Bool :=
  (waitingTiles count).all id

end IsFullWait.Decidable

def IsFullWait.decide (c : Hand n) : Bool :=
  Decidable.decide c.Valid &&
    (IsFullWait.Decidable.waitingTiles (Array.ofFn c)).all id

instance (c : Hand n) : Decidable (IsFullWait c) := by
  sorry

end Mahjong.Hand
