/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Scan

/-! Adding integer triplets leaves the canonical sequence part unchanged and
translates the triplet coefficients. Actual removal is therefore decided by
the corresponding canonical triplet coefficient. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma canonicalSequence_add_triplets (c t : VirtualHand n) (k : ℕ) (bound : k ≤ 3 * n) :
    canonicalSequence (c + (3 : ℤ) • t) k = canonicalSequence c k := by
  apply (canonicalSequence_prefix_iff _ _ k bound).mp _ k le_rfl
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
  simp [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]

@[simp]
lemma canonicalTriplet_add_triplets (c t : VirtualHand n) (i : Rank n) :
    canonicalTriplet (c + (3 : ℤ) • t) i = canonicalTriplet c i + t i := by
  have bound := i.isLt
  rw [canonicalTriplet_eq, canonicalTriplet_eq,
    canonicalSequence_add_triplets c t i.val (by omega),
    canonicalSequence_add_triplets c t (i.val - 1) (by omega)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  omega

@[simp]
lemma virtuallyMeldable_add_triplets_iff (c t : VirtualHand n) :
    VirtuallyMeldable (c + (3 : ℤ) • t) ↔ VirtuallyMeldable c := by
  rw [virtuallyMeldable_iff_size_rankSum, virtuallyMeldable_iff_size_rankSum]
  simp only [map_add, map_smul, smul_eq_mul, Int.cast_add, Int.cast_mul]
  simp [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]

lemma meldable_add_triplets_iff {c : VirtualHand n} (h : VirtuallyMeldable c)
    (t : VirtualHand n) :
    Meldable (c + (3 : ℤ) • t) ↔ ∀ i, 0 ≤ canonicalTriplet c i + t i := by
  rw [meldable_iff_scan]
  simp only [virtuallyMeldable_add_triplets_iff, h, canonicalTriplet_add_triplets, true_and]

lemma Meldable.add_triplets {c : VirtualHand n} (h : Meldable c)
    {t : VirtualHand n} (positive : 0 ≤ t) : Meldable (c + (3 : ℤ) • t) := by
  apply (meldable_add_triplets_iff h.virtuallyMeldable t).mpr
  intro i
  exact add_nonneg (h.canonicalTriplet_nonnegative i) (positive i)

lemma Meldable.add_triplet {c : VirtualHand n} (h : Meldable c) (i : Rank n) :
    Meldable (c + triplet i) := h.add_triplets (nonnegative_single i)

/-- A triplet can be removed exactly when it occurs in the canonical placement. -/
lemma Meldable.sub_triplet_iff {c : VirtualHand n} (h : Meldable c) (i : Rank n) :
    Meldable (c - triplet i) ↔ 1 ≤ canonicalTriplet c i := by
  have shape : c - triplet i = c + (3 : ℤ) • (-single i) := by
    simp [triplet, sub_eq_add_neg]
  rw [shape, meldable_add_triplets_iff h.virtuallyMeldable]
  constructor
  · intro all
    have at_i := all i
    simpa using at_i
  · intro source j
    have original := h.canonicalTriplet_nonnegative j
    simp only [Pi.neg_apply, single_apply]
    split_ifs with equal
    · subst j
      omega
    · omega

lemma Meldable.add {c d : VirtualHand n} (hc : Meldable c) (hd : Meldable d) :
    Meldable (c + d) := by
  obtain ⟨p, hp, rfl⟩ := hc
  obtain ⟨q, hq, rfl⟩ := hd
  refine ⟨⟨p.seqNum + q.seqNum, p.tripNum + q.tripNum⟩,
    ⟨add_nonneg hp.1 hq.1, add_nonneg hp.2 hq.2⟩, ?_⟩
  simp only [Placement.toHand_eq, map_add, smul_add]
  abel

end Mahjong.VirtualHand
