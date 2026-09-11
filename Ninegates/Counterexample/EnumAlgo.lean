/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Counterexample.Basic

/-!
# Finite candidates for ordinary full waits

Orders one and two share a weak-composition enumeration. Orders three through
seven enumerate candidates without an interior run of three singleton tiles.
See `EnumSpec` for the characterization of these candidates.
-/

@[expose] public section

namespace Mahjong.Hand.Counterexample

/--
Enumerate all the lists that is bounded by `bounds` and sums to `total`.
-/
def boundedLists : List Nat → Nat → List (List Nat)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | bound :: bounds, total => do
      let x ← List.range (min bound total + 1)
      let xs ← boundedLists bounds (total - x)
      pure (x :: xs)

/--
Placing positives into gaps.
A gap is a gap if it's between two positives, or if it's at the beginning or end of the list.
Positives may not be fully placed if gaps are insufficient.
-/
def placePositives : List Nat → List Nat → List Nat
  | gaps, [] => do
      let gap ← gaps
      List.replicate gap 0
  | gap :: gaps, x :: xs => List.replicate gap 0 ++ x :: placePositives gaps xs
  | [], _ :: _ => []

def largeCandidateExcesses (n : Nat) : List (List Nat) := do
  let left ← List.range 7
  let right ← List.range 7
  let excessCount ← List.range 7
  if left + right + excessCount ≤ 6 then
    let positiveExcess ← boundedLists (List.replicate excessCount 6)
      (6 - left - right - excessCount)
    let gaps ← boundedLists (List.replicate (excessCount + 1) 2)
      (3 * n - 2 - excessCount)
    let positives := positiveExcess.map (fun excess => excess + 1)
    pure (left :: placePositives gaps positives ++ [right])
  else []

/-- Shared weak-composition enumeration for orders one and two. -/
def smallCandidateExcesses (n : Nat) : List (List Nat) :=
  boundedLists (List.replicate (3 * n) 6) 6

/-- The excess vectors for ordinary full-wait candidates.  For orders one and
two all weak compositions of six are retained.  For larger orders, internal
zeros are placed in gaps of length at most two. -/
def CandidateExcesses (n : Nat) : List (List Nat) :=
  if 1 ≤ n && n ≤ 2 then
    smallCandidateExcesses n
  else if 3 ≤ n && n ≤ 7 then
    largeCandidateExcesses n
  else []

/-- Recover a hand from its boundary/interior excess vector. -/
def handOfExcess (n : Nat) (excess : List Nat) : Hand n :=
  ⟨fun i =>
    excess.getD i.val 0 + if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else 1⟩

@[grind =]
lemma handOfExcess_apply (n : Nat) (excess : List Nat) (i : Fin (3 * n)) :
    handOfExcess n excess i =
      excess.getD i.val 0 + if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else 1 := rfl

/-- The hands represented by `CandidateExcesses`. -/
def Candidates (n : Nat) : List (Hand n) :=
  (CandidateExcesses n).map (handOfExcess n)

end Mahjong.Hand.Counterexample
