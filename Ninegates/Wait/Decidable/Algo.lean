import Ninegates.Wait.Basic
import Ninegates.Winning.Decidable

/-!
# Prefix/suffix algorithm for waiting tiles

Relies on the winning check algorithm.
-/

namespace Mahjong.Hand

namespace WaitingTiles.Decidable

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
  !(stepSet (c + 1) (pref.get ⟨j.val, by omega⟩) ∩
    (suff.get ⟨j.val + 1, by omega⟩)).isEmpty

def decideCount (count : Array Nat) : Array Bool := Id.run do
  let n := count.size
  let pref := buildPrefix count
  let suff := buildSuffix count
  let mut result : Vector Bool n := Vector.replicate n false
  for j in List.finRange n do
    result := result.set j.val (waitsOn count pref suff j) (by omega)
  return result.toArray

def decide (c : Hand n) : Array Bool :=
  decideCount (Array.ofFn c)

private theorem decide_size_impl (c : Hand n) : (decide c).size = 3 * n := by
  simp [decide, decideCount]

def waitingTilesFast (c : Hand n) : Finset (Fin (3 * n)) :=
  if Hand.size c = 3 * n + 4 then
    Finset.univ.filter fun i =>
      (decide c)[i.val]'(by rw [decide_size_impl]; exact i.isLt) = true
  else
    ∅

end WaitingTiles.Decidable

namespace LiveWaitingTiles.Decidable

def decide (c : Hand n) : Array Bool :=
  let count := Array.ofFn c
  if count.all (fun x => x ≤ 4) then
    Array.zipWith (· && ·) (WaitingTiles.Decidable.decide c) (count.map (fun x => x ≤ 3))
  else
    Array.replicate count.size false

private theorem decide_size_impl (c : Hand n) : (decide c).size = 3 * n := by
  simp only [LiveWaitingTiles.Decidable.decide]
  split <;> simp [Array.size_zipWith, WaitingTiles.Decidable.decide_size_impl]

def liveWaitingTilesFast (c : Hand n) : Finset (Fin (3 * n)) :=
  if Hand.size c = 3 * n + 4 then
    Finset.univ.filter fun i =>
      (decide c)[i.val]'(by rw [decide_size_impl]; exact i.isLt) = true
  else
    ∅

end LiveWaitingTiles.Decidable

end Mahjong.Hand
