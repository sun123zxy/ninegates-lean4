/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Bounds
public import Ninegates.Meldable.Statistics

/-! Class sizes at meld count `n+1`. Congruence and the lower bounds leave two
possibilities; triplets and missing-rank separation exclude the second for `n>=2`. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n}

lemma IsFullWait.class_sizes_alternatives (h : IsFullWait (n + 1) c) (r : ZMod 3)
    (nonfixed : r ≠ fixedClass c) :
    (classSize (fixedClass c) c = n ∧ classSize r c = (n : ℤ) + 2 ∧
      classSize (pairedClass c r) c = (n : ℤ) + 2) ∨
    (classSize (fixedClass c) c = (n : ℤ) + 2 ∧ classSize r c = (n : ℤ) + 1 ∧
      classSize (pairedClass c r) c = (n : ℤ) + 1) := by
  have other_fixed : pairedClass c r ≠ fixedClass c := by simpa using nonfixed
  have other_self : pairedClass c r ≠ r :=
    fun equal ↦ nonfixed ((pairedClass_eq_self_iff c r).mp equal)
  have partition := size_eq_three_classSizes c (fixedClass c) r (pairedClass c r)
    nonfixed.symm other_fixed.symm other_self.symm
  have count : size c = 3 * (n : ℤ) + 4 := by have count := h.2.1; push_cast at count; omega
  have count_mod : (size c : ZMod 3) = 1 := by
    rw [h.2.1]
    push_cast
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
  have lower_s := h.fixed_class_size
  have lower_r := h.nonfixed_class_size r nonfixed
  have lower_other := h.nonfixed_class_size _ other_fixed
  have residue_r := (ZMod.intCast_eq_intCast_iff' (classSize r c + 1)
    (classSize (fixedClass c) c) 3).mp
      (by simpa only [Int.cast_add, Int.cast_one] using
        classSize_nonfixed_congruence count_mod r nonfixed)
  have residue_other := (ZMod.intCast_eq_intCast_iff' (classSize (pairedClass c r) c + 1)
    (classSize (fixedClass c) c) 3).mp
      (by simpa only [Int.cast_add, Int.cast_one] using
        classSize_nonfixed_congruence count_mod (pairedClass c r) other_fixed)
  omega

private lemma exceptional_triplet (fixed_size : classSize (fixedClass c) c = (n : ℤ) + 2)
    (other_sizes : ∀ r, r ≠ fixedClass c → classSize r c = (n : ℤ) + 1)
    {i j : Rank n} (edge : DrawPair c i j) (nonfixed : rankClass i ≠ fixedClass c)
    (r : ZMod 3) (relevant : r = fixedClass c ∨ r = rankClass i) :
    ∃ q : Rank n, rankClass q = r ∧ 3 ≤ (c + single i - pair j) q ∧
      Meldable (c + single i - pair j - triplet q) := by
  have pair_nonfixed : rankClass j ≠ fixedClass c :=
    fun equal ↦ nonfixed (edge.fixed_class_iff.mpr equal)
  have different := edge.nonfixed_classes nonfixed
  have small : classSize (rankClass j) (c + single i - pair j) = (n : ℤ) - 1 := by
    simp only [map_sub, map_add, classSize_pair, classSize_single,
      ite_eq_right different, ite_true, other_sizes _ pair_nonfixed]
    ring
  have large : classSize r (c + single i - pair j) = (n : ℤ) + 2 := by
    rcases relevant with rfl | rfl
    · simp only [map_sub, map_add, classSize_pair, classSize_single,
        ite_eq_right nonfixed, ite_eq_right pair_nonfixed, fixed_size]
      ring
    · simp only [map_sub, map_add, classSize_pair, classSize_single,
        ite_true, ite_eq_right different.symm, other_sizes _ nonfixed]
      ring
  exact edge.exists_triplet_of_classSize_lt r (rankClass j) (by rw [small, large]; omega)

private lemma exceptional_fixed_is_two (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (fixed_size : classSize (fixedClass c) c = (n : ℤ) + 2)
    (other_sizes : ∀ r, r ≠ fixedClass c → classSize r c = (n : ℤ) + 1) : fixedClass c = 2 := by
  by_contra not_two
  have interior_nonfixed : (2 : ZMod 3) ≠ fixedClass c := Ne.symm not_two
  have positive := h.excess_nonnegative
  have total : classSize 2 (excess c) = 1 := by
    rw [classSize_excess, other_sizes 2 interior_nonfixed, classSize_interiorOnes_two h.order_pos]
    omega
  have cap (q : Rank n) (class_q : rankClass q = 2) : c q ≤ 2 := by
    have point := positive.le_classSize q
    rw [class_q, total, excess_apply] at point
    have base := (interiorOnes_bounds q).2
    omega
  let a : Rank n := ⟨1, by omega⟩
  let b : Rank n := ⟨4, by omega⟩
  have class_a : rankClass a = 2 := by rw [rankClass_eq_two_iff]; norm_num [a]
  have class_b : rankClass b = 2 := by rw [rankClass_eq_two_iff]; norm_num [b]
  have base_a : interiorOnes a = 1 := by
    simp only [interiorOnes, a]
    split_ifs <;> omega
  have base_b : interiorOnes b = 1 := by
    simp only [interiorOnes, b]
    split_ifs <;> omega
  have either : c a ≤ 1 ∨ c b ≤ 1 := by
    have different : a ≠ b := by
      intro equal
      have values := congrArg Fin.val equal
      norm_num [a, b] at values
    have combined := positive.add_le_classSize a b different (class_b.trans class_a.symm)
    rw [class_a, total, excess_apply, excess_apply, base_a, base_b] at combined
    omega
  obtain ⟨i, class_i, small⟩ : ∃ i : Rank n, rankClass i = 2 ∧ c i ≤ 1 := by
    rcases either with small | small
    · exact ⟨a, class_a, small⟩
    · exact ⟨b, class_b, small⟩
  obtain ⟨j, edge⟩ := (isFullWait_iff.mp h).2.2 i
  obtain ⟨q, class_q, count, _⟩ := exceptional_triplet fixed_size other_sizes edge
    (by rwa [class_i]) (rankClass i) (Or.inr rfl)
  have original := cap q (class_q.trans class_i)
  have pair_nonnegative : 0 ≤ pair j q := nonnegative_pair j q
  change 3 ≤ c q + single i q - pair j q at count
  by_cases equal : q = i
  · subst q
    rw [single_self] at count
    omega
  · rw [single_of_ne equal] at count
    omega

private lemma missing_interior_class (order : 2 ≤ n) {d : VirtualHand n} (q : Rank n)
    (class_q : rankClass q = 2) (missing : d q = 0) :
    ¬(∀ i : Rank n, rankClass i ≠ 2 → ∃ j, DrawPair d i j) := by
  intro all
  have residue := (rankClass_eq_two_iff q).mp class_q
  have bound_q := q.isLt
  have inside : 0 < q.val ∧ q.val + 1 < 3 * n := by omega
  have neighbours (i : Rank n)
      (near : i.val + 1 = q.val ∨ i.val = q.val + 1 ∨
        i.val + 2 = q.val ∨ i.val = q.val + 2) : rankClass i ≠ 2 := by
    change ¬rankClass i = 2
    rw [rankClass_eq_two_iff]
    omega
  let a : Rank n := ⟨q.val - 1, by omega⟩
  let b : Rank n := ⟨q.val + 1, by omega⟩
  have left : a.val < q.val := by dsimp [a]; omega
  have right : q.val < b.val := by dsimp [b]; omega
  obtain ⟨p, ha⟩ := all a (neighbours a (Or.inl (by dsimp [a]; omega)))
  obtain ⟨r, hb⟩ := all b (neighbours b (Or.inr (Or.inl rfl)))
  have sizes := missing_side_sizes missing ha hb left right
  by_cases room : 2 ≤ q.val
  · let x : Rank n := ⟨q.val - 2, by omega⟩
    obtain ⟨j, hx⟩ := all x (neighbours x (Or.inr (Or.inr (Or.inl (by dsimp [x]; omega)))))
    have class_a := (ha.across_missing_left missing sizes.1 left).2.2
    have class_x := (hx.across_missing_left missing sizes.1 (by dsimp [x]; omega)).2.2
    have same := (rankClass_eq_iff x a).mp (class_x.trans class_a.symm)
    dsimp [x, a] at same
    omega
  · let x : Rank n := ⟨q.val + 2, by omega⟩
    obtain ⟨j, hx⟩ := all x (neighbours x (Or.inr (Or.inr (Or.inr rfl))))
    have class_b := (hb.across_missing_right missing sizes.2 right).2.2
    have class_x := (hx.across_missing_right missing sizes.2 (by dsimp [x]; omega)).2.2
    have same := (rankClass_eq_iff x b).mp (class_x.trans class_b.symm)
    dsimp [x, b] at same
    omega

private lemma exceptional_impossible (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (fixed_size : classSize (fixedClass c) c = (n : ℤ) + 2)
    (other_sizes : ∀ r, r ≠ fixedClass c → classSize r c = (n : ℤ) + 1) : False := by
  have fixed := exceptional_fixed_is_two order h fixed_size other_sizes
  have one_nonfixed : (1 : ZMod 3) ≠ fixedClass c := by
    rw [fixed]
    decide +kernel
  obtain ⟨i, class_i⟩ := exists_rankClass h.order_pos 1
  obtain ⟨j, edge⟩ := (isFullWait_iff.mp h).2.2 i
  have i_nonfixed : rankClass i ≠ fixedClass c := by rwa [class_i]
  obtain ⟨q, class_q, count, _⟩ := exceptional_triplet fixed_size other_sizes edge
    i_nonfixed (fixedClass c) (Or.inl rfl)
  have q_ne_i : q ≠ i := by
    intro equal
    exact i_nonfixed ((congrArg rankClass equal).symm.trans class_q)
  have original_q : 3 ≤ c q := by
    have pair_nonnegative : 0 ≤ pair j q := nonnegative_pair j q
    change 3 ≤ c q + single i q - pair j q at count
    rw [single_of_ne q_ne_i] at count
    omega
  have positive := h.excess_nonnegative
  have total : classSize 2 (excess c) = 2 := by
    rw [classSize_excess, ← fixed, fixed_size, fixed, classSize_interiorOnes_two h.order_pos]
    omega
  have class_q_two : rankClass q = 2 := class_q.trans fixed
  have point := positive.le_classSize q
  rw [class_q_two, total, excess_apply] at point
  have base := interiorOnes_bounds q
  have value : c q = 3 ∧ excess c q = 2 := by
    rw [excess_apply]
    omega
  have others (a : Rank n) (class_a : rankClass a = 2) (different : a ≠ q) : c a ≤ 1 := by
    have combined := positive.add_le_classSize q a different.symm (class_a.trans class_q_two.symm)
    rw [class_q_two, total, value.2, excess_apply] at combined
    have base_a := (interiorOnes_bounds a).2
    omega
  let d := c - triplet q
  have missing : d q = 0 := by simp [d, value.1]
  apply missing_interior_class order q class_q_two missing
  intro a nonfixed
  obtain ⟨b, hab⟩ := (isFullWait_iff.mp h).2.2 a
  obtain ⟨r, class_r, count_r, removable⟩ := exceptional_triplet fixed_size other_sizes hab
    (by rwa [fixed]) (fixedClass c) (Or.inl rfl)
  have class_r_two : rankClass r = 2 := class_r.trans fixed
  have r_ne_a : r ≠ a := by
    intro equal
    exact nonfixed ((congrArg rankClass equal).symm.trans class_r_two)
  have original_r : 3 ≤ c r := by
    have pair_nonnegative : 0 ≤ pair b r := nonnegative_pair b r
    change 3 ≤ c r + single a r - pair b r at count_r
    rw [single_of_ne r_ne_a] at count_r
    omega
  have same : r = q := by
    by_contra different
    have cap := others r class_r_two different
    omega
  subst r
  refine ⟨b, ?_⟩
  have equal : d + single a - pair b = c + single a - pair b - triplet q := by dsimp [d]; abel
  change Meldable (d + single a - pair b)
  rwa [equal]

/-- `prp-class-sizes-n-plus-one`, fixed class. The order-one exception is real. -/
lemma IsFullWait.fixed_class_size_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c) :
    classSize (fixedClass c) c = n := by
  by_contra different
  have nonfixed : fixedClass c + 1 ≠ fixedClass c := by simp
  have fixed_size : classSize (fixedClass c) c = (n : ℤ) + 2 := by
    rcases h.class_sizes_alternatives _ nonfixed with good | bad
    · exact (different good.1).elim
    · exact bad.1
  have other_sizes (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
      classSize r c = (n : ℤ) + 1 := by
    rcases h.class_sizes_alternatives r nonfixed with good | bad
    · exact (different good.1).elim
    · exact bad.2.1
  exact exceptional_impossible order h fixed_size other_sizes

/-- `prp-class-sizes-n-plus-one`, either interchanging class. -/
lemma IsFullWait.nonfixed_class_size_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) : classSize r c = (n : ℤ) + 2 := by
  have fixed := h.fixed_class_size_succ order
  rcases h.class_sizes_alternatives r nonfixed with good | bad
  · exact good.2.1
  · omega

end Mahjong.VirtualHand
