import Ninegates.Wait.Basic
import Ninegates.Winning.Decide

/-!
Algorithms for deciding waits and full waits.
See `Decidable` directory for specifications and proofs of correctness.
-/

namespace Mahjong.Hand

def IsWinningTile.decide (c : Hand n) (i : Fin (3 * n)) : Bool :=
  Winning.decide (c + single i)

namespace IsFullWait.Decidable

open Winning.Decidable

variable {n : ℕ}

def buildPrefix (count : Array Nat) : Array StateSet := Id.run do
  let n := count.size
  let mut pref := Array.replicate (n + 1) Bitset.empty
  pref := pref.set! 0 (Bitset.singleton State.init)
  for i in List.range n do
    pref := pref.set! (i + 1) (stepSet count[i]! pref[i]!)
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
  if count[j]! ≥ 4 then false
  else
    Bitset.nonempty (Bitset.inter (stepSet (count[j]! + 1) pref[j]!) suff[j + 1]!)

def waitingTiles (count : Array Nat) : Array Bool := Id.run do
  let n := count.size
  let pref := buildPrefix count
  let suff := buildSuffix count
  let mut result := Array.replicate n false
  for j in List.range n do
    result := result.set! j (waitsOn count pref suff j)
  return result

end IsFullWait.Decidable

def IsFullWait.decide (c : Hand n) : Bool :=
  Decidable.decide c.Valid &&
    (IsFullWait.Decidable.waitingTiles (Array.ofFn c)).all id

end Mahjong.Hand
