/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Missing

/-! Every interior rank of a full-sided wait has positive multiplicity. The
three-rank boundary case is included, rather than assuming order at least two. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n}

/-- `prp-interior-positive`, with zero-based rank indices. -/
lemma IsFullWait.interior_positive (h : IsFullWait m c) (k : Rank n)
    (left : 0 < k.val) (right : k.val + 1 < 3 * n) : 1 ≤ c k := by
  by_contra not_positive
  have nonnegative : 0 ≤ c k := h.1 k
  have missing : c k = 0 := by omega
  have all := (isFullWait_iff.mp h).2.2
  let first : Rank n := ⟨0, by omega⟩
  let last : Rank n := ⟨3 * n - 1, by omega⟩
  obtain ⟨p, first_edge⟩ := all first
  obtain ⟨q, last_edge⟩ := all last
  have sizes := missing_side_sizes missing first_edge last_edge
    (by dsimp [first]; omega) (by dsimp [last]; omega)
  have left_class (a : Rank n) (before : a.val < k.val) :
      rankClass a = -(rankSum (leftOf k c) : ZMod 3) := by
    obtain ⟨j, edge⟩ := all a
    exact (edge.across_missing_left missing sizes.1 before).2.2
  have right_class (a : Rank n) (after : k.val < a.val) :
      rankClass a = -(rankSum (rightOf k c) : ZMod 3) := by
    obtain ⟨j, edge⟩ := all a
    exact (edge.across_missing_right missing sizes.2 after).2.2
  have short_left : k.val ≤ 1 := by
    by_contra long
    let a : Rank n := ⟨0, by omega⟩
    let b : Rank n := ⟨1, by omega⟩
    have same := (left_class a (by dsimp [a]; omega)).trans
      (left_class b (by dsimp [b]; omega)).symm
    have residues := (rankClass_eq_iff a b).mp same
    norm_num [a, b] at residues
  have short_right : 3 * n ≤ k.val + 2 := by
    by_contra long
    let a : Rank n := ⟨k.val + 1, by omega⟩
    let b : Rank n := ⟨k.val + 2, by omega⟩
    have same := (right_class a (by dsimp [a]; omega)).trans
      (right_class b (by dsimp [b]; omega)).symm
    have residues := (rankClass_eq_iff a b).mp same
    dsimp [a, b] at residues
    omega
  have order_one : n = 1 := by omega
  subst n
  have middle : k.val = 1 := by omega
  have pair_after := (first_edge.across_missing_left missing sizes.1
    (by dsimp [first]; omega)).1
  have pair_last : p = last := Fin.ext (by dsimp [last]; have := p.isLt; omega)
  rw [pair_last] at first_edge
  obtain ⟨j, middle_edge⟩ := all k
  have same_sum := middle_edge.congruence.trans first_edge.congruence.symm
  have doubled : rankClass k + rankClass k = rankClass first + rankClass last := by
    simp only [rankClass, rank, middle, first, last]
    change (2 : ZMod 3) + 2 = 1 + 0
    decide +kernel
  have same_class : rankClass j = rankClass k :=
    add_left_cancel (same_sum.trans doubled.symm)
  have residues := (rankClass_eq_iff j k).mp same_class
  have same_rank : j = k := Fin.ext (by have := j.isLt; omega)
  subst j
  have available := middle_edge.self_positive
  omega

end Mahjong.VirtualHand
