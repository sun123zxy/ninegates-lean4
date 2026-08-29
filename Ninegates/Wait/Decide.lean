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

def buildPrefix (count : Array Nat) :
    Vector StateSet (count.size + 1) := Id.run do
  let n := count.size
  let mut pref : Vector StateSet (n + 1) := Vector.replicate (n + 1) emptyStateSet
  pref := pref.set 0 (emptyStateSet.insert State.init) (by omega)
  for i in List.finRange n do
    let c := count[i.val]'(by simp [n, i.isLt])
    let q := pref.get ⟨i.val, by omega⟩
    pref := pref.set (i.val + 1) (stepSet c q) (by omega)
  return pref

def buildSuffix (count : Array Nat) :
    Vector StateSet (count.size + 1) := Id.run do
  let n := count.size
  let mut suff : Vector StateSet (n + 1) := Vector.replicate (n + 1) emptyStateSet
  suff := suff.set n (emptyStateSet.insert State.final) (by omega)
  for k in List.finRange n do
    let i := n - 1 - k.val
    have hi : i < count.size := by omega
    let mut good : StateSet := emptyStateSet
    for q in State.all do
      if !(step (count[i]'hi) q ∩ (suff.get ⟨i + 1, by omega⟩)).isEmpty then
        good := good.insert q
    suff := suff.set i good (by omega)
  return suff

def waitsOn (count : Array Nat)
    (pref : Vector StateSet (count.size + 1))
    (suff : Vector StateSet (count.size + 1))
    (j : Fin count.size) : Bool :=
  let c := count[j.val]'j.isLt
  if c ≥ 4 then false
  else
    !(stepSet (c + 1) (pref.get ⟨j.val, by omega⟩) ∩
      (suff.get ⟨j.val + 1, by omega⟩)).isEmpty

def waitingTiles (count : Array Nat) : Array Bool := Id.run do
  let n := count.size
  let pref := buildPrefix count
  let suff := buildSuffix count
  let mut result : Vector Bool n := Vector.replicate n false
  for j in List.finRange n do
    result := result.set j.val (waitsOn count pref suff j) (by omega)
  return result.toArray

end IsFullWait.Decidable

def IsFullWait.decide (c : Hand n) : Bool :=
  Decidable.decide c.Valid &&
    (IsFullWait.Decidable.waitingTiles (Array.ofFn c)).all id

end Mahjong.Hand
