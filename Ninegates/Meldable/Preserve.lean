/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Moving

/-! A successful step from a rank with no canonical triplet preserves every
existing canonical triplet. This is the invariant used for consecutive edges. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

namespace Moving

lemma canonical_step_tripNum_mono {p : Placement n} (h : p.Canonic)
    (positive : p.Nonnegative) (r : Start n) (empty : p.tripNum (rankAt r 0) = 0)
    (moved : Meldable (right p.toHand r)) : p.tripNum ≤ (step p r).canonicalize.tripNum := by
  have actual : 0 ≤ (step p r).canonicalize.tripNum := by
    apply (Placement.canonic_canonicalize _).meldable_iff_tripNum_nonnegative.mp
    simpa using moved
  have source := (canonical_step_tripNum_nonnegative_iff h positive.2 r).mp actual |>.1
  have no_borrow : borrow p r = 0 := by
    rw [empty] at source
    unfold borrow at *
    split_ifs <;> omega
  rw [canonical_step_tripNum h, no_borrow, zero_smul, sub_zero]
  intro i
  have nonnegative_carry : 0 ≤ carry p r := by unfold carry; split <;> norm_num
  have gain := mul_nonneg nonnegative_carry (nonnegative_sequence (sequenceAt r 1) i)
  change p.tripNum i ≤ p.tripNum i + carry p r * sequence (sequenceAt r 1) i
  omega

/-- `prp-moving-preserves-triplets`, stated directly for the computed canonical
coefficients, without choosing placements in downstream arguments. -/
lemma canonicalTriplet_right_mono {c : VirtualHand n} (hc : Meldable c) (r : Start n)
    (empty : canonicalTriplet c (rankAt r 0) = 0) (moved : Meldable (right c r)) :
    ∀ i, canonicalTriplet c i ≤ canonicalTriplet (right c r) i := by
  obtain ⟨p, ⟨positive, canonical, rfl⟩, _⟩ := hc.unique_canonical
  rw [canonical.canonicalTriplet_eq] at empty
  have monotone := canonical_step_tripNum_mono canonical positive r empty moved
  intro i
  have trace := (Placement.canonic_canonicalize (step p r)).canonicalTriplet_eq i
  simp only [Placement.toHand_canonicalize, toHand_step] at trace
  rw [trace, canonical.canonicalTriplet_eq]
  exact monotone i

end Moving
end Mahjong.VirtualHand
