import Ninegates.Winning.Basic
import Ninegates.Bitset.Basic

/-!
Executable state-space support for deciding winning hands.
-/

namespace Mahjong.Hand

namespace Winning.Decidable

variable {n : ℕ}

structure State where
  /-- Number of sequences started at the previous position. -/
  a : Nat
  /-- Number of sequences started two positions ago. -/
  b : Nat
  /-- Whether the pair has already been used. -/
  pairUsed : Bool
deriving DecidableEq, Inhabited

namespace State

def init : State := ⟨0, 0, false⟩
def final : State := ⟨0, 0, true⟩

def all : List State :=
  (List.range 3).flatMap fun a ↦
    (List.range 3).flatMap fun b ↦
      [{a := a, b := b, pairUsed := false},
        {a := a, b := b, pairUsed := true}]

def encode (q : State) : Fin 18 :=
  ⟨q.a % 3 + 3 * (q.b % 3) + if q.pairUsed then 9 else 0, by grind⟩

end State

instance : Bitset.Encoder State where
  size := 18
  encode := State.encode

abbrev StateSet := Bitset State

def step (c : Nat) (q : State) : StateSet := Id.run do
  let mut result := Bitset.empty
  for e in [0, 1] do
    let pair : Bool := e == 1
    if q.pairUsed && pair then
      continue
    let need := q.a + q.b + 2 * e
    if need ≤ c then
      let rest := c - need
      let s := rest % 3
      result := Bitset.insert
        ({a := s, b := q.a, pairUsed := q.pairUsed || pair} : State) result
  return result

def advanceSet (c : Nat) (states : StateSet) : StateSet :=
  State.all.foldl (fun result q ↦
    if Bitset.mem states q then Bitset.union result (step c q) else result)
    Bitset.empty

/-- The executable algorithm is intentionally left for the next step. -/
def decide (c : Hand n) : Bool := by
  sorry

instance (c : Hand n) : Decidable (Winning c) := by
  sorry

end Winning.Decidable

end Mahjong.Hand
