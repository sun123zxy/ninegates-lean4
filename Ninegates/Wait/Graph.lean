/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Basic
public import Ninegates.Meldable.Interval
public import Ninegates.Meldable.Triplets

/-! Incoming intervals and bidirectional edges of the draw-pair graph. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ} {c : VirtualHand n} {i j p q : Rank n}

def fixedClass (c : VirtualHand n) : ZMod 3 := (rankSum c : ZMod 3)
def pairedClass (c : VirtualHand n) (r : ZMod 3) : ZMod 3 := -fixedClass c - r

@[simp]
lemma pairedClass_pairedClass (c : VirtualHand n) (r : ZMod 3) :
    pairedClass c (pairedClass c r) = r := by simp [pairedClass]

lemma pairedClass_eq_self_iff (c : VirtualHand n) (r : ZMod 3) :
    pairedClass c r = r ↔ r = fixedClass c := by
  have three_r : (3 : ZMod 3) * r = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  have three_s : (3 : ZMod 3) * fixedClass c = 0 := by
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
  unfold pairedClass
  constructor <;> intro equal
  · linear_combination equal + three_r
  · rw [equal]
    linear_combination -three_s

@[simp]
lemma pairedClass_eq_fixed_iff (c : VirtualHand n) (r : ZMod 3) :
    pairedClass c r = fixedClass c ↔ r = fixedClass c := by
  have fixed := (pairedClass_eq_self_iff c (fixedClass c)).mpr rfl
  constructor
  · intro equal
    simpa only [pairedClass_pairedClass, fixed] using congrArg (pairedClass c) equal
  · intro equal
    rw [equal, fixed]

lemma DrawPair.class_eq (h : DrawPair c i j) : rankClass j = pairedClass c (rankClass i) := by
  have same := h.congruence
  unfold pairedClass fixedClass
  linear_combination same

lemma DrawPair.self_fixed_class (h : DrawPair c i i) : rankClass i = fixedClass c :=
  (pairedClass_eq_self_iff c (rankClass i)).mp h.class_eq.symm

lemma DrawPair.fixed_class_iff (h : DrawPair c i j) :
    rankClass i = fixedClass c ↔ rankClass j = fixedClass c := by
  have fixed := (pairedClass_eq_self_iff c (fixedClass c)).mpr rfl
  constructor
  · intro equal
    rw [h.class_eq, equal, fixed]
  · intro equal
    have reverse_class : rankClass i = pairedClass c (rankClass j) := by
      rw [h.class_eq, pairedClass_pairedClass]
    rw [reverse_class, equal, fixed]

lemma DrawPair.nonfixed_classes (h : DrawPair c i j) (nonfixed : rankClass i ≠ fixedClass c) :
    rankClass i ≠ rankClass j := by
  intro equal
  have fixed : pairedClass c (rankClass i) = rankClass i := h.class_eq.symm.trans equal.symm
  exact nonfixed ((pairedClass_eq_self_iff c (rankClass i)).mp fixed)

lemma DrawPair.same_draw_class (hp : DrawPair c p q) (hi : DrawPair c i q) :
    rankClass p = rankClass i := by
  have first := hp.congruence
  have second := hi.congruence
  linear_combination first - second

lemma DrawPair.reverse (h : DrawPair c i j) : DrawPair (reverse c) i.rev j.rev := by
  simpa only [DrawPair, pair, map_sub, map_add, map_smul, reverse_single] using
    Meldable.reverse h

@[simp]
lemma drawPair_reverse_iff (c : VirtualHand n) (i j : Rank n) :
    DrawPair (reverse c) i.rev j.rev ↔ DrawPair c i j :=
  ⟨fun h ↦ by simpa using h.reverse, DrawPair.reverse⟩

/-- `prp-incoming-interval`: the incoming neighbours of a fixed pair form an
interval in their class. The hand may be virtual; the two edges suffice. -/
lemma DrawPair.incoming_interval (hp : DrawPair c p q) (hi : DrawPair c i q)
    (k : Rank n) (between : min p.val i.val ≤ k.val ∧ k.val ≤ max p.val i.val)
    (same : rankClass k = rankClass p) : DrawPair c k q := by
  have moving (a : Rank n) : moveTile (c + single p - pair q) p a =
      c + single a - pair q := by simp only [moveTile]; abel
  have endpoint : Meldable (moveTile (c + single p - pair q) p i) := by
    rw [moving]
    exact hi
  change Meldable (c + single k - pair q)
  simpa only [moving] using (Meldable.moveTile_interval hp endpoint between same)

@[simp]
lemma drawPair_self_iff (c : VirtualHand n) (i : Rank n) :
    DrawPair c i i ↔ Meldable (c - single i) := by
  have equal : c + single i - pair i = c - single i := by
    simp only [pair, two_smul]
    abel
  simp only [DrawPair, equal]

lemma DrawPair.augmented_meldable (h : DrawPair c i j) :
    Meldable (c + single i + single j) := by
  have equal : c + single i + single j = (c + single i - pair j) + triplet j := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply]
    ring
  rw [equal]
  exact h.add_triplet j

/-- In an augmented hand, an edge is exactly the presence of its pair's
triplet in the canonical placement. -/
lemma drawPair_iff_triplet (h : Meldable (c + single i + single j)) :
    DrawPair c i j ↔ 1 ≤ canonicalTriplet (c + single i + single j) j := by
  have equal : c + single i + single j - triplet j = c + single i - pair j := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply]
    ring
  rw [← h.sub_triplet_iff, equal]
  rfl

/-- The remainder after two distinct pairs is required to be actually meldable. -/
def TwoPair (c : VirtualHand n) (p q : Rank n) : Prop :=
  p ≠ q ∧ Meldable (c - pair p - pair q)

lemma TwoPair.comm (h : TwoPair c p q) : TwoPair c q p := by
  refine ⟨h.1.symm, ?_⟩
  have swap : c - pair q - pair p = c - pair p - pair q := by abel
  rw [swap]
  exact h.2

lemma TwoPair.drawPair (h : TwoPair c p q) : DrawPair c p q := by
  have decomposition : c + single p - pair q = (c - pair p - pair q) + triplet p := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply]
    ring
  rw [DrawPair, decomposition]
  exact h.2.add_triplet p

/-- `prp-bidirectional-two-pair`. Canonical sequence parts agree modulo three,
and the reverse edge supplies the nonnegative triplet remainder. -/
lemma bidirectional_iff_twoPair (different : p ≠ q) :
    (DrawPair c p q ∧ DrawPair c q p) ↔ TwoPair c p q := by
  constructor
  · rintro ⟨forward, backward⟩
    refine ⟨different, ?_⟩
    have shifted : c + single p - pair q =
        (c + single q - pair p) + (3 : ℤ) • (single p - single q) := by
      ext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pair_apply]
      ring
    have coefficient : 1 ≤ canonicalTriplet (c + single p - pair q) p := by
      rw [shifted, canonicalTriplet_add_triplets]
      have original := backward.canonicalTriplet_nonnegative p
      simp only [Pi.sub_apply, single_self, single_of_ne different]
      omega
    have remainder := (forward.sub_triplet_iff p).mpr coefficient
    have equal : c + single p - pair q - triplet p = c - pair p - pair q := by
      ext k
      simp only [Pi.add_apply, Pi.sub_apply, pair_apply, triplet_apply]
      ring
    rwa [equal] at remainder
  · intro h
    exact ⟨h.drawPair, h.comm.drawPair⟩

end Mahjong.VirtualHand
