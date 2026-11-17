/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Graph
public import Ninegates.Meldable.Split

/-! Waiting on both sides of a missing rank forces the winning pair onto the
opposite side from every draw, and fixes the draw class on each side. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n} {i j k : Rank n}

lemma DrawPair.pair_ne_missing (h : DrawPair c i j) (missing : c k = 0) (draw : i ≠ k) :
    j ≠ k := by
  intro equal
  subst j
  have available := h.pair_available draw
  omega

lemma DrawPair.remainder_missing (h : DrawPair c i j) (missing : c k = 0) (draw : i ≠ k) :
    (c + single i - pair j) k = 0 := by
  have pair := h.pair_ne_missing missing draw
  simp only [Pi.sub_apply, Pi.add_apply, missing, pair_apply, single_of_ne draw.symm,
    single_of_ne pair.symm, mul_zero, add_zero, sub_zero]

lemma DrawPair.leftOf_missing (h : DrawPair c i j) (missing : c k = 0) (draw : i ≠ k) :
    Meldable (leftOf k c + (if i.val < k.val then single i else 0) -
      (if j.val < k.val then pair j else 0)) := by
  simpa only [map_sub, map_add, leftOf_single, leftOf_pair] using
    Meldable.leftOf h k (h.remainder_missing missing draw)

lemma DrawPair.rightOf_missing (h : DrawPair c i j) (missing : c k = 0) (draw : i ≠ k) :
    Meldable (rightOf k c + (if k.val < i.val then single i else 0) -
      (if k.val < j.val then pair j else 0)) := by
  simpa only [map_sub, map_add, rightOf_single, rightOf_pair] using
    Meldable.rightOf h k (h.remainder_missing missing draw)

private lemma size_mod_of_meldable {d : VirtualHand n} (h : Meldable d) : size d % 3 = 0 := by
  simpa using (ZMod.intCast_eq_intCast_iff' (size d) 0 3).mp h.virtuallyMeldable.size_cast

lemma DrawPair.missing_size_residues (h : DrawPair c i j) (missing : c k = 0) (draw : i ≠ k) :
    size (leftOf k c) % 3 =
        ((if j.val < k.val then 2 else 0) - (if i.val < k.val then 1 else 0)) % 3 ∧
      size (rightOf k c) % 3 =
        ((if k.val < j.val then 2 else 0) - (if k.val < i.val then 1 else 0)) % 3 := by
  have left := size_mod_of_meldable (h.leftOf_missing missing draw)
  have right := size_mod_of_meldable (h.rightOf_missing missing draw)
  simp only [map_sub, map_add, apply_ite, map_zero, size_single, size_pair] at left right
  split_ifs at * <;> omega

/-- The residue conclusion of `prp-waits-across-missing-rank`. Two edges with
draws on opposite sides suffice; no fixed meld count is needed. -/
lemma missing_side_sizes {a b p q : Rank n} (missing : c k = 0)
    (ha : DrawPair c a p) (hb : DrawPair c b q) (left : a.val < k.val) (right : k.val < b.val) :
    size (leftOf k c) % 3 = 2 ∧ size (rightOf k c) % 3 = 2 := by
  have a_ne : a ≠ k := by intro equal; subst a; omega
  have b_ne : b ≠ k := by intro equal; subst b; omega
  have p_ne := ha.pair_ne_missing missing a_ne
  have q_ne := hb.pair_ne_missing missing b_ne
  have pair_p : p.val ≠ k.val := fun equal ↦ p_ne (Fin.ext equal)
  have pair_q : q.val ≠ k.val := fun equal ↦ q_ne (Fin.ext equal)
  have a_sizes := ha.missing_size_residues missing a_ne
  have b_sizes := hb.missing_size_residues missing b_ne
  split_ifs at * <;> omega

lemma DrawPair.across_missing_left (h : DrawPair c i j) (missing : c k = 0)
    (left_size : size (leftOf k c) % 3 = 2) (left : i.val < k.val) :
    k.val < j.val ∧ Meldable (leftOf k c + single i) ∧
      rankClass i = -(rankSum (leftOf k c) : ZMod 3) := by
  have draw : i ≠ k := by intro equal; subst i; omega
  have pair := h.pair_ne_missing missing draw
  have sizes := (h.missing_size_residues missing draw).1
  have opposite : k.val < j.val := by
    have different : j.val ≠ k.val := fun equal ↦ pair (Fin.ext equal)
    split_ifs at sizes <;> omega
  have actual : Meldable (leftOf k c + single i) := by
    have cut := h.leftOf_missing missing draw
    simpa only [ite_eq_left left, ite_eq_right (show ¬j.val < k.val by omega), sub_zero] using cut
  refine ⟨opposite, actual, ?_⟩
  have weighted := actual.virtuallyMeldable.rankSum_cast
  simp only [map_add, rankSum_single, Int.cast_add] at weighted
  change (rankSum (leftOf k c) : ZMod 3) + rankClass i = 0 at weighted
  linear_combination weighted

lemma DrawPair.across_missing_right (h : DrawPair c i j) (missing : c k = 0)
    (right_size : size (rightOf k c) % 3 = 2) (right : k.val < i.val) :
    j.val < k.val ∧ Meldable (rightOf k c + single i) ∧
      rankClass i = -(rankSum (rightOf k c) : ZMod 3) := by
  have draw : i ≠ k := by intro equal; subst i; omega
  have pair := h.pair_ne_missing missing draw
  have sizes := (h.missing_size_residues missing draw).2
  have opposite : j.val < k.val := by
    have different : j.val ≠ k.val := fun equal ↦ pair (Fin.ext equal)
    split_ifs at sizes <;> omega
  have actual : Meldable (rightOf k c + single i) := by
    have cut := h.rightOf_missing missing draw
    simpa only [ite_eq_left right, ite_eq_right (show ¬k.val < j.val by omega), sub_zero] using cut
  refine ⟨opposite, actual, ?_⟩
  have weighted := actual.virtuallyMeldable.rankSum_cast
  simp only [map_add, rankSum_single, Int.cast_add] at weighted
  change (rankSum (rightOf k c) : ZMod 3) + rankClass i = 0 at weighted
  linear_combination weighted

/-- `prp-incoming-edges-both-sides`: a pair used by draws on both sides has at
least three original copies, not merely the two needed to form the pair. -/
lemma DrawPair.incoming_both_sides {a b : Rank n} (ha : DrawPair c a j)
    (hb : DrawPair c b j) (left : a.val < j.val) (right : j.val < b.val) : 3 ≤ c j := by
  have a_ne : a ≠ j := by intro equal; subst a; omega
  have b_ne : b ≠ j := by intro equal; subst b; omega
  have available := ha.pair_available a_ne
  by_contra too_small
  have exactly : c j = 2 := by omega
  let d := c - pair j
  have missing : d j = 0 := by simp [d, exactly]
  have left_draw : Meldable (d + single a) := by
    have equal : d + single a = c + single a - pair j := by dsimp [d]; abel
    rwa [equal]
  have right_draw : Meldable (d + single b) := by
    have equal : d + single b = c + single b - pair j := by dsimp [d]; abel
    rwa [equal]
  have zero_left : (d + single a) j = 0 := by
    simp only [Pi.add_apply, missing, single_of_ne a_ne.symm, zero_add]
  have zero_right : (d + single b) j = 0 := by
    simp only [Pi.add_apply, missing, single_of_ne b_ne.symm, zero_add]
  have left_part := left_draw.leftOf j zero_left
  have right_part := right_draw.leftOf j zero_right
  simp only [map_add, leftOf_single, ite_eq_left left] at left_part
  simp only [map_add, leftOf_single, ite_eq_right (show ¬b.val < j.val by omega),
    add_zero] at right_part
  have count_left := size_mod_of_meldable left_part
  have count_right := size_mod_of_meldable right_part
  simp only [map_add, size_single] at count_left
  omega

end Mahjong.VirtualHand
