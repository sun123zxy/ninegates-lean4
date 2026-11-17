/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Virtual

/-!
# The triplet-greedy scan

`canonicalSequence c j` is the paper's `σ_j`, including `σ_0 = 0`. The
integer sequence recovery, reduced modulo three, satisfies the canonical
recurrence. This gives an explicit scan without choosing an existential
placement. Triplet coefficients are integer Euclidean quotients.
-/

@[expose] public section

namespace Mahjong.VirtualHand

namespace SequenceScan

lemma run_map {R S : Type*} [AddCommGroup R] [AddCommGroup S]
    (f : R →+ S) (a : ℕ → R) (k : ℕ) :
    run (fun j ↦ f (a j)) k = (f (run a k).1, f (run a k).2) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [run, ih, map_sub]

end SequenceScan

variable {n : ℕ}

def canonicalSequence (c : VirtualHand n) (j : ℕ) : ℤ := (sequenceScan c j).1 % 3

def canonicalTriplet (c : VirtualHand n) (i : Rank n) : ℤ :=
  (c i - canonicalSequence c (i.val + 1) - canonicalSequence c i.val -
    canonicalSequence c (i.val - 1)) / 3

def scanPlacement (c : VirtualHand n) : Placement n where
  seqNum j := canonicalSequence c (j.val + 1)
  tripNum i := canonicalTriplet c i

@[simp]
lemma canonicalSequence_zero (c : VirtualHand n) : canonicalSequence c 0 = 0 := rfl

lemma canonicalSequence_bounds (c : VirtualHand n) (j : ℕ) :
    0 ≤ canonicalSequence c j ∧ canonicalSequence c j < 3 :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

lemma canonicalSequence_previous (c : VirtualHand n) (k : ℕ) :
    (sequenceScan c k).2 % 3 = canonicalSequence c (k - 1) := by
  cases k <;> rfl

lemma canonicalSequence_succ (c : VirtualHand n) (k : ℕ) :
    canonicalSequence c (k + 1) = (coefficient c (k : ℤ) - canonicalSequence c k -
      canonicalSequence c (k - 1)) % 3 := by
  change (coefficient c (k : ℤ) - (sequenceScan c k).1 - (sequenceScan c k).2) % 3 =
    (coefficient c (k : ℤ) - (sequenceScan c k).1 % 3 - canonicalSequence c (k - 1)) % 3
  rw [← canonicalSequence_previous c k]
  omega

lemma canonicalTriplet_eq (c : VirtualHand n) (i : Rank n) :
    canonicalTriplet c i =
      (c i - canonicalSequence c i.val - canonicalSequence c (i.val - 1)) / 3 := by
  unfold canonicalTriplet
  rw [canonicalSequence_succ, coefficient_fin]
  omega

lemma tripletGreedy_identity (c : VirtualHand n) (i : Rank n) :
    c i = canonicalSequence c (i.val + 1) + canonicalSequence c i.val +
      canonicalSequence c (i.val - 1) + 3 * canonicalTriplet c i := by
  unfold canonicalTriplet
  rw [canonicalSequence_succ, coefficient_fin]
  omega

namespace Placement

lemma sequenceScan_cast (p : Placement n) (k : ℕ) (bound : k ≤ 3 * n) :
    (((sequenceScan p.toHand k).1 : ZMod 3), ((sequenceScan p.toHand k).2 : ZMod 3)) =
      (((coefficient p.seqNum ((k : ℤ) - 1) : ℤ) : ZMod 3),
       ((coefficient p.seqNum ((k : ℤ) - 2) : ℤ) : ZMod 3)) := by
  have same : ∀ j < k, ((coefficient p.toHand (j : ℤ) : ℤ) : ZMod 3) =
      coefficient (fun i ↦ (p.seqNum i : ZMod 3)) (j : ℤ) +
      coefficient (fun i ↦ (p.seqNum i : ZMod 3)) ((j : ℤ) - 1) +
      coefficient (fun i ↦ (p.seqNum i : ZMod 3)) ((j : ℤ) - 2) := by
    intro j inside
    let i : Rank n := ⟨j, by omega⟩
    rw [coefficient_fin p.toHand i]
    have coordinate := congrArg (fun z : ℤ ↦ (z : ZMod 3)) (toHand_apply p i)
    push_cast at coordinate
    have three : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    simpa only [coefficient_intCast, three, zero_mul, add_zero] using coordinate
  have mapped := (SequenceScan.run_map (Int.castAddHom (ZMod 3))
    (fun j ↦ coefficient p.toHand (j : ℤ)) k).symm
  calc
    _ = SequenceScan.run (fun j ↦ ((coefficient p.toHand (j : ℤ) : ℤ) : ZMod 3)) k := mapped
    _ = SequenceScan.run (fun j ↦ coefficient (fun i ↦ (p.seqNum i : ZMod 3)) (j : ℤ) +
        coefficient (fun i ↦ (p.seqNum i : ZMod 3)) ((j : ℤ) - 1) +
        coefficient (fun i ↦ (p.seqNum i : ZMod 3)) ((j : ℤ) - 2)) k :=
      SequenceScan.run_congr k same
    _ = _ := by
      simpa only [coefficient_intCast] using
        SequenceScan.run_of_coefficients (fun i ↦ (p.seqNum i : ZMod 3)) k

lemma Canonic.canonicalSequence_eq {p : Placement n} (h : p.Canonic) (k : ℕ) (bound : k ≤ 3 * n) :
    canonicalSequence p.toHand k = coefficient p.seqNum ((k : ℤ) - 1) := by
  have equal := congrArg Prod.fst (sequenceScan_cast p k bound)
  have rem := (ZMod.intCast_eq_intCast_iff' _ _ 3).mp equal
  have bounded := h.coefficient_bounds ((k : ℤ) - 1)
  simpa [canonicalSequence, Int.emod_eq_of_lt bounded.1 bounded.2] using rem

lemma Canonic.canonicalTriplet_eq {p : Placement n} (h : p.Canonic) (i : Rank n) :
    canonicalTriplet p.toHand i = p.tripNum i := by
  have previous : canonicalSequence p.toHand (i.val - 1) =
      coefficient p.seqNum ((i.val : ℤ) - 2) := by
    by_cases first : i.val = 0
    · simp [first]
    · rw [h.canonicalSequence_eq (i.val - 1) (by have bound := i.isLt; omega)]
      congr 1
      omega
  unfold canonicalTriplet
  rw [h.canonicalSequence_eq (i.val + 1) (by have bound := i.isLt; omega),
    h.canonicalSequence_eq i.val (by have bound := i.isLt; omega), previous]
  have index : ((i.val + 1 : ℕ) : ℤ) - 1 = (i.val : ℤ) := by omega
  rw [index]
  have coordinate := toHand_apply p i
  omega

lemma Canonic.scanPlacement_eq {p : Placement n} (h : p.Canonic) : scanPlacement p.toHand = p := by
  apply Placement.ext
  · ext j
    simpa [scanPlacement] using
      h.canonicalSequence_eq (j.val + 1) (by have bound := j.isLt; omega)
  · ext i
    exact h.canonicalTriplet_eq i

end Placement

lemma scanPlacement_canonic (c : VirtualHand n) : (scanPlacement c).Canonic :=
  fun j ↦ canonicalSequence_bounds c (j.val + 1)

lemma scanPlacement_toHand {c : VirtualHand n} (h : VirtuallyMeldable c) :
    (scanPlacement c).toHand = c := by
  obtain ⟨p, ⟨canonical, equal⟩, _⟩ := h.unique_canonical
  simpa only [equal] using congrArg Placement.toHand canonical.scanPlacement_eq

@[simp]
lemma scanPlacement_of_placement (p : Placement n) : scanPlacement p.toHand = p.canonicalize := by
  simpa using p.canonic_canonicalize.scanPlacement_eq

lemma canonicalSequence_boundary (c : VirtualHand n) :
    (canonicalSequence c (3 * n), canonicalSequence c (3 * n - 1)) =
      ((classSize 0 c - classSize 2 c) % 3, (classSize 2 c - classSize 1 c) % 3) := by
  apply Prod.ext
  · change canonicalSequence c (3 * n) = _
    unfold canonicalSequence
    rw [sequenceScan_boundary]
  · change canonicalSequence c (3 * n - 1) = _
    rw [← canonicalSequence_previous c (3 * n), sequenceScan_boundary]

lemma virtuallyMeldable_iff_canonicalSequence (c : VirtualHand n) : VirtuallyMeldable c ↔
    canonicalSequence c (3 * n) = 0 ∧ canonicalSequence c (3 * n - 1) = 0 := by
  have first : canonicalSequence c (3 * n) = (classSize 0 c - classSize 2 c) % 3 :=
    congrArg Prod.fst (canonicalSequence_boundary c)
  have second : canonicalSequence c (3 * n - 1) = (classSize 2 c - classSize 1 c) % 3 :=
    congrArg Prod.snd (canonicalSequence_boundary c)
  rw [virtuallyMeldable_iff_classSizes, first, second]
  simp only [ZMod.intCast_eq_intCast_iff']
  norm_num only [Nat.cast_ofNat]
  omega

lemma meldable_iff_scan (c : VirtualHand n) : Meldable c ↔
    VirtuallyMeldable c ∧ ∀ i, 0 ≤ canonicalTriplet c i := by
  constructor
  · intro meldable
    have virtual := meldable.virtuallyMeldable
    have criterion := (scanPlacement_canonic c).meldable_iff_tripNum_nonnegative
    rw [scanPlacement_toHand virtual] at criterion
    exact ⟨virtual, criterion.mp meldable⟩
  · rintro ⟨virtual, nonnegative⟩
    have criterion := (scanPlacement_canonic c).meldable_iff_tripNum_nonnegative
    rw [scanPlacement_toHand virtual] at criterion
    exact criterion.mpr nonnegative

/-- Both right-end conditions and all nonnegative triplet quotients are needed. -/
lemma meldable_iff_tripletGreedy (c : VirtualHand n) : Meldable c ↔
    (canonicalSequence c (3 * n) = 0 ∧ canonicalSequence c (3 * n - 1) = 0) ∧
      ∀ i, 0 ≤ canonicalTriplet c i := by
  rw [meldable_iff_scan, virtuallyMeldable_iff_canonicalSequence]

lemma canonicalSequence_eq_iff_cast (c d : VirtualHand n) (k : ℕ) :
    canonicalSequence c k = canonicalSequence d k ↔
      ((sequenceScan c k).1 : ZMod 3) = ((sequenceScan d k).1 : ZMod 3) := by
  simpa [canonicalSequence] using
    (ZMod.intCast_eq_intCast_iff' (sequenceScan c k).1 (sequenceScan d k).1 3).symm

/-- `prp-canonical-sequence-congruence`, including the common initial value at zero. -/
lemma canonicalSequence_prefix_iff (c d : VirtualHand n) (k : ℕ) (bound : k ≤ 3 * n) :
    (∀ i : Rank n, i.val < k → (c i : ZMod 3) = (d i : ZMod 3)) ↔
      ∀ j ≤ k, canonicalSequence c j = canonicalSequence d j := by
  constructor
  · intro same j inside
    apply (canonicalSequence_eq_iff_cast c d j).mpr
    have inputs : ∀ l < j, ((coefficient c (l : ℤ) : ℤ) : ZMod 3) =
        ((coefficient d (l : ℤ) : ℤ) : ZMod 3) := by
      intro l hl
      let i : Rank n := ⟨l, by omega⟩
      rw [coefficient_fin c i, coefficient_fin d i]
      exact same i (by change l < k; omega)
    have trace := SequenceScan.run_congr j inputs
    have mapped_c := SequenceScan.run_map (Int.castAddHom (ZMod 3))
      (fun l ↦ coefficient c (l : ℤ)) j
    have mapped_d := SequenceScan.run_map (Int.castAddHom (ZMod 3))
      (fun l ↦ coefficient d (l : ℤ)) j
    simp only [Int.coe_castAddHom] at mapped_c mapped_d
    rw [mapped_c, mapped_d] at trace
    exact congrArg Prod.fst trace
  · intro same i inside
    have hc := tripletGreedy_identity c i
    have hd := tripletGreedy_identity d i
    rw [same (i.val + 1) (by omega), same i.val (by omega), same (i.val - 1) (by omega)] at hc
    apply (ZMod.intCast_eq_intCast_iff' _ _ 3).mpr
    norm_num only [Nat.cast_ofNat]
    omega

/-- Exact agreement of a hand prefix determines its triplet quotients as well
as its sequence residues. No meldability assumption is needed. -/
lemma canonicalTriplet_prefix_eq {c d : VirtualHand n} {k : ℕ} (bound : k ≤ 3 * n)
    (same : ∀ i : Rank n, i.val < k → c i = d i) :
    ∀ i : Rank n, i.val < k → canonicalTriplet c i = canonicalTriplet d i := by
  have sequences := (canonicalSequence_prefix_iff c d k bound).mp
    (fun i inside ↦ congrArg (fun z : ℤ ↦ (z : ZMod 3)) (same i inside))
  intro i inside
  simp only [canonicalTriplet, same i inside, sequences (i.val + 1) (by omega),
    sequences i.val (by omega), sequences (i.val - 1) (by omega)]

lemma Meldable.canonicalTriplet_nonnegative {c : VirtualHand n} (h : Meldable c) :
    ∀ i, 0 ≤ canonicalTriplet c i := ((meldable_iff_scan c).mp h).2

end Mahjong.VirtualHand
