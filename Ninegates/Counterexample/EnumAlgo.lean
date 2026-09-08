/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Counterexample.Basic

/-!
# Finite candidates for minimal counterexamples

This file contains the enumeration algorithm for generating
small candidates for minimal counterexamples.
See `EnumSpec` for it's completeness.
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
  let left ← List.range 4
  let right ← List.range 4
  let excessCount ← List.range 7
  if left + right + excessCount ≤ 6 then
    let positiveExcess ← boundedLists (List.replicate excessCount 1)
      (6 - left - right - excessCount)
    let gaps ← boundedLists (List.replicate (excessCount + 1) 2)
      (3 * n - 2 - excessCount)
    let positives := positiveExcess.map (fun excess => excess + 1)
    pure (left :: placePositives gaps positives ++ [right])
  else []

/-- The excess vectors satisfying the necessary numerical conditions for a
minimal live counterexample of small order.  Boundary entries have bound `3`,
interior entries have bound `2`, and their total is `6`. -/
def MinimalCandidateExcesses (n : Nat) : List (List Nat) :=
  if n == 2 then
    boundedLists (3 :: List.replicate (3 * n - 2) 2 ++ [3]) 6
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

/-- The hands represented by `MinimalCandidateExcesses`. -/
def MinimalCandidates (n : Nat) : List (Hand n) :=
  (MinimalCandidateExcesses n).map (handOfExcess n)

end Mahjong.Hand.Counterexample
