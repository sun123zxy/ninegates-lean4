/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates
public import ComparatorChallenges.Model

/-! The solution-side connection between the trusted statement model and the
library. The challenge never imports this module. -/

@[expose] public section

namespace ComparatorChallenges.Bridges

open Mahjong Mahjong.VirtualHand

lemma coefficient_eq {N : ℕ} {R : Type*} [Zero R] (s : Fin N → R) (k : ℤ) :
    Spec.coefficient s k = coefficient s k := rfl

lemma sequential_iff {n : ℕ} (c : VirtualHand n) : Spec.Sequential c ↔ Sequential c := Iff.rfl

lemma canonic_iff {n : ℕ} (p : Placement n) : Spec.Placement.Canonic p ↔ p.Canonic := Iff.rfl

lemma rankAt_eq {n : ℕ} (r : Spec.Moving.Start n) (i : Fin 4) :
    Spec.Moving.rankAt r i = Moving.rankAt r i := rfl

lemma right_eq {n : ℕ} (c : VirtualHand n) (r : Spec.Moving.Start n) :
    Spec.Moving.right c r = Moving.right c r := rfl

lemma run_eq {R : Type*} [AddCommGroup R] (a : ℕ → R) (k : ℕ) :
    Spec.SequenceScan.run a k = SequenceScan.run a k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Spec.SequenceScan.run, SequenceScan.run, ih]

lemma sequenceScan_eq {n : ℕ} (c : VirtualHand n) (k : ℕ) :
    Spec.sequenceScan c k = sequenceScan c k :=
  run_eq (fun j ↦ coefficient c (j : ℤ)) k

lemma recoveredSequences_eq {n : ℕ} (c : VirtualHand n) :
    Spec.recoveredSequences c = recoveredSequences c := by
  funext r
  exact congrArg Prod.fst (sequenceScan_eq c (r.val + 1))

lemma canonicalSequence_eq {n : ℕ} (c : VirtualHand n) (k : ℕ) :
    Spec.canonicalSequence c k = canonicalSequence c k := by
  exact congrArg (fun pair : ℤ × ℤ ↦ pair.1 % 3) (sequenceScan_eq c k)

lemma canonicalTriplet_eq {n : ℕ} (c : VirtualHand n) (i : Rank n) :
    Spec.canonicalTriplet c i = canonicalTriplet c i := by
  simp only [Spec.canonicalTriplet, Mahjong.VirtualHand.canonicalTriplet, canonicalSequence_eq]

lemma scanPlacement_eq {n : ℕ} (c : VirtualHand n) : Spec.scanPlacement c = scanPlacement c := by
  apply Placement.ext
  · funext r
    exact canonicalSequence_eq c (r.val + 1)
  · funext i
    exact canonicalTriplet_eq c i

end ComparatorChallenges.Bridges
