module

public import Ninegates.Winning.Basic
public import Std.Data.ExtHashSet.Basic

/-!
## Algorithms for deciding winning hands

See `Decidable` directory for specifications and proofs of correctness.
-/

@[expose] public section

namespace Mahjong.Hand

namespace Winning

namespace Decidable

variable {n : ℕ}

structure State where
  /-- Number of sequences started at the previous position. -/
  a : Fin 3
  /-- Number of sequences started two positions ago. -/
  b : Fin 3
  /-- Whether the pair has already been used. -/
  pairUsed : Bool
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

namespace State

def init : State := ⟨0, 0, false⟩
def final : State := ⟨0, 0, true⟩

def all : List State :=
  (List.finRange 3).flatMap fun a ↦
    (List.finRange 3).flatMap fun b ↦
      [{a := a, b := b, pairUsed := false},
        {a := a, b := b, pairUsed := true}]

def encode (q : State) : Fin 18 :=
  ⟨q.a.val + 3 * q.b.val + if q.pairUsed then 9 else 0, by grind⟩

end State

instance : Hashable State where
  hash q := UInt64.ofNat (State.encode q).val

abbrev StateSet := Std.ExtHashSet State

abbrev emptyStateSet : StateSet :=
  Std.ExtHashSet.emptyWithCapacity 32

def step (c : Nat) (q : State) : StateSet := Id.run do
  let mut result := emptyStateSet
  for e in [0, 1] do
    let pair : Bool := e == 1
    if q.pairUsed && pair then
      continue
    let need := q.a.val + q.b.val + 2 * e
    if need ≤ c then
      let rest := c - need
      let s : Fin 3 := ⟨rest % 3, by grind⟩
      result := result.insert
        ({a := s, b := q.a, pairUsed := q.pairUsed || pair} : State)
  return result

def stepSet (c : Nat) (states : StateSet) : StateSet :=
  State.all.foldl (fun result q ↦
    if states.contains q then result ∪ step c q else result)
    emptyStateSet

end Decidable

open Winning.Decidable

def decide (c : Hand n) : Bool := Id.run do
  if Hand.size c != 3 * n + 5 then return false
  let mut states : StateSet := emptyStateSet |>.insert State.init
  for x in List.ofFn c do
    states := stepSet x states
  return states.contains State.final

end Winning

end Mahjong.Hand
