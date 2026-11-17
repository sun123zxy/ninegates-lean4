/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.PillarPair
public import Ninegates.Wait.PillarPlacements

/-! Removing the two pairs leaves `n` sequences. Moving a tile from either
pillar to any rank in its own class preserves sequential meldability. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n} {p q : Rank n}

namespace Pillars

lemma fixed_draw_sequential_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) {i j : Rank n} (edge : DrawPair c i j)
    (fixed_i : rankClass i = fixedClass c) :
    Sequential (c + single i - pair j - triplet p - triplet q) := by
  obtain ⟨t, positive, equal⟩ := edge
  have shape := full.fixed_draw_placement_succ order p q pillars.pillar_p pillars.pillar_q
    pillars.nonfixed_p pillars.class_q ⟨t, positive, equal⟩ fixed_i positive equal
  have representation := t.toHand_eq
  rw [shape.2, equal, smul_add] at representation
  change c + single i - pair j = sequenceHand t.seqNum + (triplet p + triplet q) at representation
  refine ⟨t.seqNum, positive.1, ?_⟩
  rw [representation]
  abel

lemma nonfixed_draw_placement_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) {i : Rank n} (class_i : rankClass i = rankClass p)
    {t : Placement n} (positive : t.Nonnegative) (equal : t.toHand = c + single i - pair q) :
    t.sequenceCount = n ∧ t.tripNum = single p := by
  have class_sizes (r : ZMod 3) : classSize r (c + single i - pair q) =
      classSize r c + (if rankClass i = r then 1 else 0) -
        2 * (if rankClass q = r then 1 else 0) := by
    simp only [map_sub, map_add, classSize_pair, classSize_single]
  have fixed_size : classSize (fixedClass c) (c + single i - pair q) = n := by
    rw [class_sizes, class_i, ite_eq_right pillars.nonfixed_p,
      ite_eq_right pillars.nonfixed_q, full.fixed_class_size_succ order]
    omega
  have q_size : classSize (rankClass q) (c + single i - pair q) = n := by
    rw [class_sizes, class_i, ite_eq_right pillars.different_classes,
      ite_eq_left rfl, full.nonfixed_class_size_succ order _ pillars.nonfixed_q]
    omega
  have p_size : classSize (rankClass p) (c + single i - pair q) = (n : ℤ) + 3 := by
    rw [class_sizes, class_i, ite_eq_left rfl, ite_eq_right pillars.different_classes.symm,
      full.nonfixed_class_size_succ order _ pillars.nonfixed_p]
    omega
  have fixed_zero (k : Rank n) (fixed_k : rankClass k = fixedClass c) : t.tripNum k = 0 := by
    have different : k ≠ i := by
      intro same
      have fixed_i := (congrArg rankClass same).symm.trans fixed_k
      rw [class_i] at fixed_i
      exact pillars.nonfixed_p fixed_i
    have bound := positive.triplet_le_hand k
    rw [equal] at bound
    change 3 * t.tripNum k ≤ c k + single i k - pair q k at bound
    rw [single_of_ne different] at bound
    have original := full.fixed_count_succ order k fixed_k
    have pair_nonnegative : 0 ≤ pair q k := nonnegative_pair q k
    have nonnegative : 0 ≤ t.tripNum k := positive.2 k
    omega
  have sequence_count : t.sequenceCount = n := by
    have count := t.classSize_toHand (fixedClass c)
    rw [equal, fixed_size, classSize_eq_zero _ fixed_zero] at count
    omega
  have q_count : classSize (rankClass q) t.tripNum = 0 := by
    have count := t.classSize_toHand (rankClass q)
    rw [equal, q_size, sequence_count] at count
    omega
  have support (k : Rank n) (different : k ≠ p) : t.tripNum k = 0 := by
    have nonnegative : 0 ≤ t.tripNum k := positive.2 k
    rcases three_classes_exhaust (fixedClass c) (rankClass p) (rankClass q)
        pillars.nonfixed_p.symm pillars.nonfixed_q.symm pillars.different_classes (rankClass k)
        with fixed | left | right
    · exact fixed_zero k fixed
    · have bound := positive.triplet_le_hand k
      rw [equal] at bound
      change 3 * t.tripNum k ≤ c k + single i k - pair q k at bound
      have pair_nonnegative : 0 ≤ pair q k := nonnegative_pair q k
      by_contra nonzero
      have original : 2 ≤ c k := by
        simp only [single_apply] at bound
        split_ifs at bound <;> omega
      exact different (pillars.pillar_p.2 k left original)
    · have bound := Nonnegative.le_classSize positive.2 k
      rw [right, q_count] at bound
      omega
  have p_count : t.tripNum p = 1 := by
    have count := t.classSize_toHand (rankClass p)
    rw [equal, p_size, sequence_count, classSize_eq_single p (fun k _ ↦ support k)] at count
    omega
  refine ⟨sequence_count, ?_⟩
  ext k
  by_cases same : k = p
  · subst k
    simpa using p_count
  · simpa only [single_of_ne same] using support k same

/-- Part (3) of `prp-draw-pair-n-plus-one`, oriented from the first pillar. -/
lemma sequential_move_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) (i : Rank n) (class_i : rankClass i = rankClass p) :
    Sequential (moveTile (c - pair p - pair q) p i) := by
  have edge := (pillars.drawPair_iff full class_i).mpr rfl
  obtain ⟨t, positive, equal⟩ := edge
  have shape := pillars.nonfixed_draw_placement_succ order full class_i positive equal
  have representation := t.toHand_eq
  rw [shape.2, equal] at representation
  change c + single i - pair q = sequenceHand t.seqNum + triplet p at representation
  have moved : moveTile (c - pair p - pair q) p i = c + single i - pair q - triplet p := by
    ext k
    simp only [moveTile, Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply]
    ring
  refine ⟨t.seqNum, positive.1, ?_⟩
  rw [moved, representation, add_sub_cancel_right]

lemma remainder_sequential_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) : Sequential (c - pair p - pair q) := by
  simpa using pillars.sequential_move_succ order full p rfl

lemma remainder_sequential_moves_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) :
    Sequential (c - pair p - pair q) ∧ size (c - pair p - pair q) = 3 * (n : ℤ) ∧
      (∀ i : Rank n, rankClass i = rankClass p →
        Sequential (moveTile (c - pair p - pair q) p i)) ∧
      (∀ i : Rank n, rankClass i = rankClass q →
        Sequential (moveTile (c - pair p - pair q) q i)) := by
  refine ⟨pillars.remainder_sequential_succ order full, ?_,
    fun i same ↦ pillars.sequential_move_succ order full i same, ?_⟩
  · simp only [map_sub, size_pair, full.2.1]
    push_cast
    ring
  · intro i same
    have swapped := pillars.swap.sequential_move_succ order full i same
    have equal : c - pair q - pair p = c - pair p - pair q := by abel
    rwa [equal] at swapped

end Pillars
end Mahjong.VirtualHand
