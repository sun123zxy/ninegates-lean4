/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Pillars

/-! Every winning placement of a fixed-class draw consists of `n-1` sequences
and exactly one triplet at each pillar. This concerns all actual placements. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

lemma IsFullWait.fixed_draw_count_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    {i j : Rank n} (edge : DrawPair c i j) (fixed_i : rankClass i = fixedClass c)
    (k : Rank n) (fixed_k : rankClass k = fixedClass c) :
    (c + single i - pair j) k ≤ 2 := by
  have original := h.fixed_count_succ order k fixed_k
  have pair_nonnegative : 0 ≤ pair j k := nonnegative_pair j k
  change c k + single i k - pair j k ≤ 2
  by_cases same : k = i
  · subst k
    rw [single_self]
    by_cases equal : i = j
    · subst j
      simp only [pair_apply, single_self]
      omega
    · have available := edge.pair_available equal
      have fixed_j := edge.fixed_class_iff.mp fixed_i
      have small : c i ≤ 1 := by
        by_contra big
        exact equal (h.fixed_pair_unique_succ order fixed_i fixed_j (by omega) available)
      omega
  · rw [single_of_ne same]
    omega

/-- Part (3) of `prp-unique-pair-ranks`, with the complete triplet vector. -/
lemma IsFullWait.fixed_draw_placement_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (p q : Rank n) (pillar_p : Pillar c p) (pillar_q : Pillar c q)
    (nonfixed : rankClass p ≠ fixedClass c) (other : rankClass q = pairedClass c (rankClass p))
    {i j : Rank n} (edge : DrawPair c i j) (fixed_i : rankClass i = fixedClass c)
    {t : Placement n} (positive : t.Nonnegative) (equal : t.toHand = c + single i - pair j) :
    t.sequenceCount = (n : ℤ) - 1 ∧ t.tripNum = single p + single q := by
  have other_nonfixed : rankClass q ≠ fixedClass c := by simpa only [Ne, other,
    pairedClass_eq_fixed_iff] using nonfixed
  have different_classes : rankClass p ≠ rankClass q := by
    rw [other]
    intro same
    exact nonfixed ((pairedClass_eq_self_iff c (rankClass p)).mp same.symm)
  have different : p ≠ q := fun same ↦ different_classes (congrArg rankClass same)
  have sizes := h.fixed_draw_classSizes_succ order edge fixed_i
  have fixed_zero (k : Rank n) (fixed_k : rankClass k = fixedClass c) : t.tripNum k = 0 := by
    have count := positive.triplet_le_hand k
    rw [equal] at count
    have cap := h.fixed_draw_count_succ order edge fixed_i k fixed_k
    have nonnegative : 0 ≤ t.tripNum k := positive.2 k
    omega
  have sequence_count : t.sequenceCount = (n : ℤ) - 1 := by
    have count := t.classSize_toHand (fixedClass c)
    rw [classSize_eq_zero _ fixed_zero, equal, sizes.1] at count
    omega
  have support (b : Rank n) (pillar : Pillar c b) (nonfixed_b : rankClass b ≠ fixedClass c)
      (k : Rank n) (class_k : rankClass k = rankClass b) (different : k ≠ b) :
      t.tripNum k = 0 := by
    have small : c k ≤ 1 := by
      by_contra big
      exact different (pillar.2 k class_k (by omega))
    have no_draw : k ≠ i := by
      intro same
      exact nonfixed_b (class_k.symm.trans ((congrArg rankClass same).trans fixed_i))
    have count := positive.triplet_le_hand k
    rw [equal] at count
    change 3 * t.tripNum k ≤ c k + single i k - pair j k at count
    rw [single_of_ne no_draw] at count
    have pair_nonnegative : 0 ≤ pair j k := nonnegative_pair j k
    have nonnegative : 0 ≤ t.tripNum k := positive.2 k
    omega
  have count_p : t.tripNum p = 1 := by
    have count := t.classSize_toHand (rankClass p)
    rw [equal, sizes.2 _ nonfixed, sequence_count,
      classSize_eq_single p (support p pillar_p nonfixed)] at count
    omega
  have count_q : t.tripNum q = 1 := by
    have count := t.classSize_toHand (rankClass q)
    rw [equal, sizes.2 _ other_nonfixed, sequence_count,
      classSize_eq_single q (support q pillar_q other_nonfixed)] at count
    omega
  refine ⟨sequence_count, ?_⟩
  ext k
  by_cases at_p : k = p
  · subst k
    simp [count_p, different, single]
  by_cases at_q : k = q
  · subst k
    simp [count_q, different.symm, single]
  simp only [Pi.add_apply, single_of_ne at_p, single_of_ne at_q, zero_add]
  rcases three_classes_exhaust (fixedClass c) (rankClass p) (rankClass q)
      nonfixed.symm other_nonfixed.symm different_classes (rankClass k) with fixed | left | right
  · exact fixed_zero k fixed
  · exact support p pillar_p nonfixed k left at_p
  · exact support q pillar_q other_nonfixed k right at_q

end Mahjong.VirtualHand
