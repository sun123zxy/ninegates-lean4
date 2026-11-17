/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Sequence

/-!
# Canonical virtual meld placements

Canonicalization uses Euclidean division in the integers, including for negative
sequence coefficients. Three copies of a sequence are replaced by its three
triplets. The resulting placement represents exactly the same virtual hand.
-/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

namespace Placement

def Canonic (p : Placement n) : Prop := ∀ j, 0 ≤ p.seqNum j ∧ p.seqNum j < 3

def canonicalize (p : Placement n) : Placement n where
  seqNum j := p.seqNum j % 3
  tripNum i := p.tripNum i + coefficient (fun j ↦ p.seqNum j / 3) i.val +
    coefficient (fun j ↦ p.seqNum j / 3) ((i.val : ℤ) - 1) +
    coefficient (fun j ↦ p.seqNum j / 3) ((i.val : ℤ) - 2)

lemma canonicalize_tripNum (p : Placement n) :
    p.canonicalize.tripNum = p.tripNum + sequenceHand (fun j ↦ p.seqNum j / 3) := by
  ext i
  simp only [canonicalize, Pi.add_apply, sequenceHand_apply]
  ring

lemma canonic_canonicalize (p : Placement n) : p.canonicalize.Canonic := by
  intro j
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

@[simp]
lemma toHand_canonicalize (p : Placement n) : p.canonicalize.toHand = p.toHand := by
  ext i
  simp only [toHand_apply, canonicalize, coefficient_emod, coefficient_ediv]
  have current := Int.emod_add_mul_ediv (coefficient p.seqNum i.val) 3
  have previous := Int.emod_add_mul_ediv (coefficient p.seqNum ((i.val : ℤ) - 1)) 3
  have older := Int.emod_add_mul_ediv (coefficient p.seqNum ((i.val : ℤ) - 2)) 3
  omega

lemma nonnegative_canonicalize {p : Placement n} (h : p.Nonnegative) :
    p.canonicalize.Nonnegative := by
  have quotient_nonneg (k : ℤ) : 0 ≤ coefficient (fun j ↦ p.seqNum j / 3) k := by
    unfold coefficient
    split
    · exact Int.ediv_nonneg (h.1 _) (by decide)
    · exact le_refl _
  refine ⟨fun j ↦ (canonic_canonicalize p j).1, ?_⟩
  intro i
  exact add_nonneg (add_nonneg (add_nonneg (h.2 i) (quotient_nonneg _))
    (quotient_nonneg _)) (quotient_nonneg _)

/-- The sequence coefficients modulo three depend only on the hand modulo three. -/
lemma seqNum_cast_eq {p q : Placement n}
    (same : ∀ i, (p.toHand i : ZMod 3) = (q.toHand i : ZMod 3)) :
    ∀ j, (p.seqNum j : ZMod 3) = (q.seqNum j : ZMod 3) := by
  have equal : (fun j ↦ (p.seqNum j : ZMod 3)) = (fun j ↦ (q.seqNum j : ZMod 3)) := by
    apply coefficients_ext
    intro j
    let i : Rank n := ⟨j.val, by omega⟩
    have at_i := same i
    simp only [toHand_apply] at at_i
    push_cast at at_i
    have three : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    simp only [three, zero_mul, add_zero] at at_i
    simpa only [coefficient_intCast] using at_i
  exact congrFun equal

lemma Canonic.seqNum_eq {p q : Placement n} (hp : p.Canonic) (hq : q.Canonic)
    (same : ∀ i, (p.toHand i : ZMod 3) = (q.toHand i : ZMod 3)) : p.seqNum = q.seqNum := by
  have residue := seqNum_cast_eq same
  ext j
  have rem := (ZMod.intCast_eq_intCast_iff' _ _ 3).mp (residue j)
  simpa [Int.emod_eq_of_lt (hp j).1 (hp j).2,
    Int.emod_eq_of_lt (hq j).1 (hq j).2] using rem

lemma canonic_unique {p q : Placement n} (hp : p.Canonic) (hq : q.Canonic)
    (same : p.toHand = q.toHand) : p = q := by
  have sequences := hp.seqNum_eq hq
    (fun i ↦ congrArg (fun z : ℤ ↦ (z : ZMod 3)) (congrFun same i))
  have triplets : p.tripNum = q.tripNum := by
    ext i
    have at_i := congrFun same i
    simp only [toHand_apply, sequences] at at_i
    omega
  exact Placement.ext sequences triplets

lemma Canonic.coefficient_bounds {p : Placement n} (h : p.Canonic) (k : ℤ) :
    0 ≤ coefficient p.seqNum k ∧ coefficient p.seqNum k < 3 := by
  unfold coefficient
  split
  · exact h _
  · norm_num

lemma Canonic.canonicalize_eq {p : Placement n} (h : p.Canonic) : p.canonicalize = p :=
  canonic_unique p.canonic_canonicalize h p.toHand_canonicalize

@[simp]
lemma canonicalize_canonicalize (p : Placement n) : p.canonicalize.canonicalize = p.canonicalize :=
  p.canonic_canonicalize.canonicalize_eq

@[simp]
lemma meldCount_canonicalize (p : Placement n) : p.canonicalize.meldCount = p.meldCount := by
  have counts := congrArg size p.toHand_canonicalize
  simp only [size_toHand] at counts
  omega

end Placement

lemma VirtuallyMeldable.unique_canonical {c : VirtualHand n} (h : VirtuallyMeldable c) :
    ∃! p : Placement n, p.Canonic ∧ p.toHand = c := by
  obtain ⟨p, equal⟩ := h
  refine ⟨p.canonicalize, ⟨p.canonic_canonicalize, by simpa using equal⟩, ?_⟩
  intro q hq
  exact Placement.canonic_unique hq.1 p.canonic_canonicalize
    (hq.2.trans (by simpa using equal.symm))

lemma Meldable.unique_canonical {c : VirtualHand n} (h : Meldable c) :
    ∃! p : Placement n, p.Nonnegative ∧ p.Canonic ∧ p.toHand = c := by
  obtain ⟨p, nonnegative, equal⟩ := h
  refine ⟨p.canonicalize,
    ⟨Placement.nonnegative_canonicalize nonnegative, p.canonic_canonicalize,
      by simpa using equal⟩, ?_⟩
  intro q hq
  exact Placement.canonic_unique hq.2.1 p.canonic_canonicalize
    (hq.2.2.trans (by simpa using equal.symm))

lemma Placement.Canonic.meldable_iff {p : Placement n} (h : p.Canonic) :
    Meldable p.toHand ↔ p.Nonnegative := by
  constructor
  · intro meldable
    obtain ⟨q, ⟨nonnegative, canonical, equal⟩, _⟩ := meldable.unique_canonical
    have same : q = p := Placement.canonic_unique canonical h equal
    simpa only [same] using nonnegative
  · intro nonnegative
    exact ⟨p, nonnegative, rfl⟩

/-- Once a canonical virtual placement is known, only triplet nonnegativity
remains to decide actual meldability. -/
lemma Placement.Canonic.meldable_iff_tripNum_nonnegative {p : Placement n} (h : p.Canonic) :
    Meldable p.toHand ↔ 0 ≤ p.tripNum := by
  rw [h.meldable_iff]
  exact ⟨And.right, fun nonnegative ↦ ⟨fun j ↦ (h j).1, nonnegative⟩⟩

end Mahjong.VirtualHand
