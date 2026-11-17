/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.ClassSizes

/-! The two pillars of a full wait with `n+1` melds: each nonfixed class has
exactly one rank that can supply an original pair, and it has at least three copies. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

def Pillar (c : VirtualHand n) (p : Rank n) : Prop :=
  3 ≤ c p ∧ ∀ a : Rank n, rankClass a = rankClass p → 2 ≤ c a → a = p

private lemma fixed_excess (order : 2 ≤ n) (h : IsFullWait (n + 1) c) :
    classSize (fixedClass c) (excess c) ≤ 1 := by
  rw [classSize_excess, h.fixed_class_size_succ order]
  have lower := classSize_interiorOnes_ge h.order_pos (fixedClass c)
  omega

lemma IsFullWait.fixed_count_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (i : Rank n) (fixed : rankClass i = fixedClass c) : c i ≤ 2 := by
  have point := h.excess_nonnegative.le_classSize i
  rw [fixed, excess_apply] at point
  have total := fixed_excess order h
  have base := (interiorOnes_bounds i).2
  omega

lemma IsFullWait.fixed_pair_unique_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    {i j : Rank n} (fixed_i : rankClass i = fixedClass c) (fixed_j : rankClass j = fixedClass c)
    (pair_i : 2 ≤ c i) (pair_j : 2 ≤ c j) : i = j := by
  by_contra different
  have combined := h.excess_nonnegative.add_le_classSize i j different (fixed_j.trans fixed_i.symm)
  rw [fixed_i, excess_apply, excess_apply] at combined
  have total := fixed_excess order h
  have base_i := (interiorOnes_bounds i).2
  have base_j := (interiorOnes_bounds j).2
  omega

lemma IsFullWait.fixed_draw_classSizes_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    {i j : Rank n} (edge : DrawPair c i j) (fixed : rankClass i = fixedClass c) :
    classSize (fixedClass c) (c + single i - pair j) = (n : ℤ) - 1 ∧
      ∀ r, r ≠ fixedClass c → classSize r (c + single i - pair j) = (n : ℤ) + 2 := by
  have fixed_j := edge.fixed_class_iff.mp fixed
  constructor
  · simp only [map_sub, map_add, classSize_pair, classSize_single, fixed, fixed_j,
      ite_true, h.fixed_class_size_succ order]
    ring
  · intro r nonfixed
    simp only [map_sub, map_add, classSize_pair, classSize_single, fixed, fixed_j,
      ite_eq_right nonfixed.symm, h.nonfixed_class_size_succ order r nonfixed]
    ring

private lemma nonfixed_triplet_exists (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
    ∃ p : Rank n, rankClass p = r ∧ 3 ≤ c p := by
  obtain ⟨i, fixed_i⟩ := exists_rankClass h.order_pos (fixedClass c)
  obtain ⟨j, edge⟩ := (isFullWait_iff.mp h).2.2 i
  have sizes := h.fixed_draw_classSizes_succ order edge fixed_i
  obtain ⟨p, class_p, count, _⟩ := edge.exists_triplet_of_classSize_lt r (fixedClass c)
    (by rw [sizes.1, sizes.2 r nonfixed]; omega)
  refine ⟨p, class_p, ?_⟩
  have different : p ≠ i := by
    intro equal
    exact nonfixed (class_p.symm.trans ((congrArg rankClass equal).trans fixed_i))
  have pair_nonnegative : 0 ≤ pair j p := nonnegative_pair j p
  change 3 ≤ c p + single i p - pair j p at count
  rw [single_of_ne different] at count
  omega

private lemma nonfixed_triplet_cap (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    {r : ZMod 3} (nonfixed : r ≠ fixedClass c) {p : Rank n}
    (class_p : rankClass p = r) (triplet : 3 ≤ c p) :
    c p ≤ 4 ∧ ∀ a : Rank n, rankClass a = r → a ≠ p → c a ≤ 2 := by
  have positive := h.excess_nonnegative
  have total : classSize r (excess c) ≤ 3 := by
    rw [classSize_excess, h.nonfixed_class_size_succ order r nonfixed]
    have lower := classSize_interiorOnes_ge h.order_pos r
    omega
  have point := positive.le_classSize p
  rw [class_p, excess_apply] at point
  have base := (interiorOnes_bounds p).2
  refine ⟨by omega, ?_⟩
  intro a class_a different
  have combined := positive.add_le_classSize p a different.symm (class_a.trans class_p.symm)
  rw [class_p, excess_apply, excess_apply] at combined
  have base_a := (interiorOnes_bounds a).2
  omega

private lemma forced_triplet {d : VirtualHand n} (actual : Meldable d) (p : Rank n)
    (s : ZMod 3) (gap : classSize s d < classSize (rankClass p) d)
    (others : ∀ a, rankClass a = rankClass p → a ≠ p → d a ≤ 2) :
    Meldable (d - triplet p) := by
  obtain ⟨a, class_a, count, removable⟩ :=
    actual.exists_triplet_of_classSize_lt (rankClass p) s gap
  have same : a = p := by
    by_contra different
    have cap := others a class_a different
    omega
  rwa [same] at removable

private lemma remove_two_triplets (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) {p q : Rank n}
    (class_p : rankClass p = r) (class_q : rankClass q = pairedClass c r)
    (triplet_p : 3 ≤ c p) (triplet_q : 3 ≤ c q) {i j : Rank n}
    (edge : DrawPair c i j) (fixed_i : rankClass i = fixedClass c) :
    DrawPair (c - triplet p - triplet q) i j := by
  have other_nonfixed : pairedClass c r ≠ fixedClass c := by simpa using nonfixed
  have different_classes : pairedClass c r ≠ r :=
    fun equal ↦ nonfixed ((pairedClass_eq_self_iff c r).mp equal)
  have sizes := h.fixed_draw_classSizes_succ order edge fixed_i
  have cap_p := (nonfixed_triplet_cap order h nonfixed class_p triplet_p).2
  have cap_q := (nonfixed_triplet_cap order h other_nonfixed class_q triplet_q).2
  have no_draw (a : Rank n) (class_a : rankClass a ≠ fixedClass c) : a ≠ i := by
    intro equal
    exact class_a ((congrArg rankClass equal).trans fixed_i)
  have first : Meldable (c + single i - pair j - triplet p) := by
    apply forced_triplet edge p (fixedClass c)
    · rw [class_p, sizes.1, sizes.2 r nonfixed]
      omega
    · intro a class_a different
      have original := cap_p a (class_a.trans class_p) different
      have zero := single_of_ne (i := i) (no_draw a (by rwa [class_a, class_p]))
      have pair_nonnegative : 0 ≤ pair j a := nonnegative_pair j a
      change c a + single i a - pair j a ≤ 2
      rw [zero]
      omega
  have second : Meldable (c + single i - pair j - triplet p - triplet q) := by
    apply forced_triplet first q (fixedClass c)
    · have keep (s : ZMod 3) (different : r ≠ s) :
          classSize s (c + single i - pair j - triplet p) =
            classSize s (c + single i - pair j) := by
        rw [map_sub, classSize_triplet, classSize_single, class_p, ite_eq_right different,
          mul_zero, sub_zero]
      rw [keep _ nonfixed, class_q, keep _ different_classes.symm, sizes.1,
        sizes.2 _ other_nonfixed]
      omega
    · intro a class_a different
      have original := cap_q a (class_a.trans class_q) different
      have zero := single_of_ne (i := i) (no_draw a (by rwa [class_a, class_q]))
      have pair_nonnegative : 0 ≤ pair j a := nonnegative_pair j a
      have triplet_nonnegative : 0 ≤ triplet p a := nonnegative_triplet p a
      change c a + single i a - pair j a - triplet p a ≤ 2
      rw [zero]
      omega
  have equal : c - triplet p - triplet q + single i - pair j =
      c + single i - pair j - triplet p - triplet q := by abel
  change Meldable (c - triplet p - triplet q + single i - pair j)
  rwa [equal]

private lemma extra_pair (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    {r : ZMod 3} (nonfixed : r ≠ fixedClass c) {p a : Rank n}
    (class_p : rankClass p = r) (class_a : rankClass a = r) (different : p ≠ a)
    (triplet : 3 ≤ c p) (pair : 2 ≤ c a) :
    c p = 3 ∧ interiorOnes p = 1 ∧ r ≠ 2 := by
  have combined := h.excess_nonnegative.add_le_classSize p a different (class_a.trans class_p.symm)
  rw [class_p, classSize_excess, h.nonfixed_class_size_succ order r nonfixed] at combined
  have lower := classSize_interiorOnes_ge h.order_pos r
  have base_p := interiorOnes_bounds p
  have base_a := interiorOnes_bounds a
  simp only [excess_apply] at combined
  refine ⟨by omega, by omega, ?_⟩
  intro equal
  rw [equal, classSize_interiorOnes_two h.order_pos] at combined
  omega

/-- Parts (1) and (2) of `prp-unique-pair-ranks`: every nonfixed class has one
pillar, and even multiplicity two is unique in its class. -/
lemma IsFullWait.exists_pillar (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
    ∃ p : Rank n, rankClass p = r ∧ Pillar c p ∧ c p ≤ 4 := by
  obtain ⟨p, class_p, triplet_p⟩ := nonfixed_triplet_exists order h r nonfixed
  have other_nonfixed : pairedClass c r ≠ fixedClass c := by simpa using nonfixed
  have different_classes : pairedClass c r ≠ r :=
    fun equal ↦ nonfixed ((pairedClass_eq_self_iff c r).mp equal)
  obtain ⟨q, class_q, triplet_q⟩ := nonfixed_triplet_exists order h _ other_nonfixed
  have different : p ≠ q := by
    intro equal
    have same := class_p.symm.trans ((congrArg rankClass equal).trans class_q)
    exact different_classes same.symm
  refine ⟨p, class_p, ⟨triplet_p, ?_⟩,
    (nonfixed_triplet_cap order h nonfixed class_p triplet_p).1⟩
  intro a class_a pair_a
  by_contra not_unique
  obtain ⟨count_p, base_p, boundary⟩ := extra_pair order h nonfixed class_p
    (class_a.trans class_p) (Ne.symm not_unique) triplet_p pair_a
  have inside : 0 < p.val ∧ p.val + 1 < 3 * n := by
    by_contra outside
    have zero : interiorOnes p = 0 := by simp only [interiorOnes, ite_eq_right outside]
    omega
  have residue : p.val % 3 ≠ 1 := by
    intro equal
    exact boundary (class_p.symm.trans ((rankClass_eq_two_iff p).mpr equal))
  have room_left : 2 ≤ p.val := by omega
  have room_right : p.val + 2 < 3 * n := by omega
  let d := c - triplet p - triplet q
  have missing : d p = 0 := by
    simp only [d, Pi.sub_apply, triplet_apply, single_self, single_of_ne different, count_p]
    norm_num
  have fixed_counts (j : Rank n) (fixed_j : rankClass j = fixedClass c) : d j = c j := by
    have jp : j ≠ p := by
      intro equal
      exact nonfixed (class_p.symm.trans ((congrArg rankClass equal).symm.trans fixed_j))
    have jq : j ≠ q := by
      intro equal
      exact other_nonfixed (class_q.symm.trans ((congrArg rankClass equal).symm.trans fixed_j))
    simp only [d, Pi.sub_apply, triplet_apply, single_of_ne jp, single_of_ne jq,
      mul_zero, sub_zero]
  obtain ⟨u, before, _, fixed_u⟩ := exists_class_before p room_left (fixedClass c)
    (by rw [class_p]; exact nonfixed.symm)
  obtain ⟨v, after, _, fixed_v⟩ := exists_class_after p room_right (fixedClass c)
    (by rw [class_p]; exact nonfixed.symm)
  obtain ⟨j, hu⟩ := (isFullWait_iff.mp h).2.2 u
  obtain ⟨k, hv⟩ := (isFullWait_iff.mp h).2.2 v
  have fixed_j := hu.fixed_class_iff.mp fixed_u
  have fixed_k := hv.fixed_class_iff.mp fixed_v
  have left_edge : DrawPair d u j :=
    remove_two_triplets order h r nonfixed class_p class_q triplet_p triplet_q hu fixed_u
  have right_edge : DrawPair d v k :=
    remove_two_triplets order h r nonfixed class_p class_q triplet_p triplet_q hv fixed_v
  have sizes := missing_side_sizes missing left_edge right_edge before after
  have j_after := (left_edge.across_missing_left missing sizes.1 before).1
  have k_before := (right_edge.across_missing_right missing sizes.2 after).1
  have uj : u ≠ j := by intro equal; have := congrArg Fin.val equal; omega
  have vk : v ≠ k := by intro equal; have := congrArg Fin.val equal; omega
  have pair_j := left_edge.pair_available uj
  have pair_k := right_edge.pair_available vk
  rw [fixed_counts j fixed_j] at pair_j
  rw [fixed_counts k fixed_k] at pair_k
  have equal := h.fixed_pair_unique_succ order fixed_j fixed_k pair_j pair_k
  have := congrArg Fin.val equal
  omega

lemma IsFullWait.unique_pair_rank_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
    ∃! p : Rank n, rankClass p = r ∧ 2 ≤ c p := by
  obtain ⟨p, class_p, pillar, _⟩ := h.exists_pillar order r nonfixed
  refine ⟨p, ⟨class_p, by have := pillar.1; omega⟩, ?_⟩
  intro a ha
  exact pillar.2 a (ha.1.trans class_p.symm) ha.2

end Mahjong.VirtualHand
