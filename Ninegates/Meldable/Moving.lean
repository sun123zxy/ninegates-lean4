/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Reverse
public import Ninegates.Meldable.Scan

/-! Moving a tile by three ranks. The virtual update replaces one sequence by
its right neighbour. Canonicalization then performs precisely one possible
borrow and one possible carry of three sequences into triplets. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

def moveTile (c : VirtualHand n) (i j : Rank n) : VirtualHand n := c - single i + single j

@[simp]
lemma moveTile_self (c : VirtualHand n) (i : Rank n) : moveTile c i i = c := by
  simp [moveTile]

@[simp]
lemma moveTile_comp (c : VirtualHand n) (i j k : Rank n) :
    moveTile (moveTile c i j) j k = moveTile c i k := by
  simp only [moveTile]
  abel

@[simp]
lemma reverse_moveTile (c : VirtualHand n) (i j : Rank n) :
    reverse (moveTile c i j) = moveTile (reverse c) i.rev j.rev := by
  simp [moveTile]

namespace Moving

/-- A legal start for a rightward step of length three. -/
abbrev Start (n : ℕ) := Fin (3 * n - 3)

def rankAt (r : Start n) (d : Fin 4) : Rank n := ⟨r.val + d.val, by omega⟩
def sequenceAt (r : Start n) (d : Fin 2) : Fin (3 * n - 2) :=
  ⟨r.val + d.val, by omega⟩

@[simp, grind =]
lemma rankAt_val (r : Start n) (d : Fin 4) : (rankAt r d).val = r.val + d.val := rfl

@[simp, grind =]
lemma sequenceAt_val (r : Start n) (d : Fin 2) :
    (sequenceAt r d).val = r.val + d.val := rfl

def right (c : VirtualHand n) (r : Start n) : VirtualHand n :=
  c - single (rankAt r 0) + single (rankAt r 3)

@[grind =]
lemma sequenceAt_apply (r : Start n) (d : Fin 2) (i : Rank n) :
    sequence (sequenceAt r d) i =
      if r.val + d.val ≤ i.val ∧ i.val ≤ r.val + d.val + 2 then 1 else 0 := by
  simp only [sequence, Pi.add_apply, single_apply, Fin.ext_iff, sequenceAt_val]
  split_ifs <;> simp_all
  all_goals omega

lemma sequence_difference (r : Start n) :
    sequence (sequenceAt r 1) - sequence (sequenceAt r 0) =
      -single (rankAt r 0) + single (rankAt r 3) := by
  have first : (⟨(sequenceAt r 1).val, by omega⟩ : Rank n) = rankAt r 1 := rfl
  have second : (⟨(sequenceAt r 1).val + 1, by omega⟩ : Rank n) = rankAt r 2 := by
    apply Fin.ext; simp
  have third : (⟨(sequenceAt r 1).val + 2, by omega⟩ : Rank n) = rankAt r 3 := by
    apply Fin.ext; simp
  simp only [sequence, first, second, third]
  change single (rankAt r 1) + single (rankAt r 2) + single (rankAt r 3) -
    (single (rankAt r 0) + single (rankAt r 1) + single (rankAt r 2)) = _
  abel

/-- The unique virtual sequence update for a single rightward step. -/
def shift (s : Fin (3 * n - 2) → ℤ) (r : Start n) : Fin (3 * n - 2) → ℤ :=
  s - Pi.single (sequenceAt r 0) 1 + Pi.single (sequenceAt r 1) 1

@[simp]
lemma sequenceHand_shift (s : Fin (3 * n - 2) → ℤ) (r : Start n) :
    sequenceHand (shift s r) = right (sequenceHand s) r := by
  simp only [shift, map_add, map_sub, sequenceHand_single, one_smul]
  rw [show sequenceHand s - sequence (sequenceAt r 0) + sequence (sequenceAt r 1) =
    sequenceHand s + (sequence (sequenceAt r 1) - sequence (sequenceAt r 0)) by abel,
    sequence_difference]
  simp only [right, sub_eq_add_neg, add_assoc]

lemma shift_nonnegative_iff {s : Fin (3 * n - 2) → ℤ} (h : 0 ≤ s) (r : Start n) :
    0 ≤ shift s r ↔ 1 ≤ s (sequenceAt r 0) := by
  have different : sequenceAt r 0 ≠ sequenceAt r 1 := by
    intro equal; have := congrArg Fin.val equal; simp at this
  constructor
  · intro positive
    have at_source := positive (sequenceAt r 0)
    simpa [shift, Pi.single_apply, different] using at_source
  · intro source j
    have at_j := h j
    simp only [shift, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> subst_vars <;> simp_all
    all_goals omega

lemma sequential_right_iff {s : Fin (3 * n - 2) → ℤ} (h : 0 ≤ s) (r : Start n) :
    Sequential (right (sequenceHand s) r) ↔ 1 ≤ s (sequenceAt r 0) := by
  rw [← sequenceHand_shift]
  constructor
  · rintro ⟨t, positive, same⟩
    have equal := sequenceHand_injective same
    exact (shift_nonnegative_iff h r).mp (equal ▸ positive)
  · intro source
    exact ⟨shift s r, (shift_nonnegative_iff h r).mpr source, rfl⟩

def step (p : Placement n) (r : Start n) : Placement n where
  seqNum := shift p.seqNum r
  tripNum := p.tripNum

@[simp]
lemma toHand_step (p : Placement n) (r : Start n) :
    (step p r).toHand = right p.toHand r := by
  rw [Placement.toHand_eq]
  change sequenceHand (shift p.seqNum r) + (3 : ℤ) • p.tripNum = _
  rw [sequenceHand_shift, Placement.toHand_eq]
  dsimp only [right]
  abel

def borrow (p : Placement n) (r : Start n) : ℤ :=
  if p.seqNum (sequenceAt r 0) = 0 then 1 else 0

def carry (p : Placement n) (r : Start n) : ℤ :=
  if p.seqNum (sequenceAt r 1) = 2 then 1 else 0

lemma quotient_step {p : Placement n} (h : p.Canonic) (r : Start n) :
    (fun j ↦ (step p r).seqNum j / 3) =
      -borrow p r • Pi.single (sequenceAt r 0) 1 +
        carry p r • Pi.single (sequenceAt r 1) 1 := by
  ext j
  have bound := h j
  have different : sequenceAt r 0 ≠ sequenceAt r 1 := by
    intro equal; have := congrArg Fin.val equal; simp at this
  simp only [step, shift, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, borrow, carry]
  split_ifs <;> subst_vars <;> simp_all <;> omega

/-- The sequence update after borrowing and carrying. Together with the
triplet update below, this specifies the resulting canonical placement. -/
lemma canonical_step_seqNum {p : Placement n} (h : p.Canonic) (r : Start n) :
    (step p r).canonicalize.seqNum = shift p.seqNum r +
      (3 * borrow p r) • Pi.single (sequenceAt r 0) 1 -
      (3 * carry p r) • Pi.single (sequenceAt r 1) 1 := by
  ext j
  have quotient := congrFun (quotient_step h r) j
  have division := Int.emod_add_mul_ediv ((step p r).seqNum j) 3
  change (shift p.seqNum r j) % 3 + 3 * ((step p r).seqNum j / 3) =
    shift p.seqNum r j at division
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at quotient
  simp only [Placement.canonicalize, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (shift p.seqNum r j) % 3 = _
  linear_combination division - 3 * quotient

/-- The entire triplet update, including the overlap of the borrow and carry. -/
lemma canonical_step_tripNum {p : Placement n} (h : p.Canonic) (r : Start n) :
    (step p r).canonicalize.tripNum = p.tripNum -
      borrow p r • sequence (sequenceAt r 0) + carry p r • sequence (sequenceAt r 1) := by
  rw [Placement.canonicalize_tripNum, quotient_step h]
  simp only [map_add, map_smul, sequenceHand_single, one_smul]
  change p.tripNum + _ = _
  simp only [neg_smul, sub_eq_add_neg, add_assoc]

lemma canonical_step_tripNum_nonnegative_iff {p : Placement n} (h : p.Canonic)
    (positive : 0 ≤ p.tripNum) (r : Start n) :
    0 ≤ (step p r).canonicalize.tripNum ↔
      borrow p r ≤ p.tripNum (rankAt r 0) ∧
      borrow p r - carry p r ≤ p.tripNum (rankAt r 1) ∧
      borrow p r - carry p r ≤ p.tripNum (rankAt r 2) := by
  have nonnegative_carry : 0 ≤ carry p r := by unfold carry; split <;> norm_num
  rw [canonical_step_tripNum h]
  constructor
  · intro result
    have first := result (rankAt r 0)
    have second := result (rankAt r 1)
    have third := result (rankAt r 2)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sequenceAt_apply, rankAt_val, Fin.val_zero, Fin.val_one, Nat.add_zero] at first second third
    simp at first second third
    omega
  · rintro ⟨first, second, third⟩ i
    have original := positive i
    have one : i.val = r.val → i = rankAt r 0 := fun eq ↦ Fin.ext (by simpa using eq)
    have two : i.val = r.val + 1 → i = rankAt r 1 := fun eq ↦ Fin.ext (by simpa using eq)
    have three : i.val = r.val + 2 → i = rankAt r 2 := fun eq ↦ Fin.ext (by simpa using eq)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sequenceAt_apply,
      Fin.val_zero, Fin.val_one, Nat.add_zero]
    by_cases a : i.val = r.val
    · simp only [one a] at *
      simp at *
      omega
    by_cases b : i.val = r.val + 1
    · simp only [two b] at *
      simp at *
      omega
    by_cases c : i.val = r.val + 2
    · simp only [three c] at *
      simp at *
      omega
    have absent : ¬(r.val ≤ i.val ∧ i.val ≤ r.val + 2) := by omega
    split_ifs <;> simp_all
    all_goals omega

/-- The four mutually exclusive rows of the paper's rightward tile-moving table. -/
lemma meldable_right_iff {p : Placement n} (h : p.Canonic) (positive : p.Nonnegative)
    (r : Start n) :
    Meldable (right p.toHand r) ↔
      (1 ≤ p.seqNum (sequenceAt r 0) ∧ p.seqNum (sequenceAt r 1) ≤ 1) ∨
      (1 ≤ p.seqNum (sequenceAt r 0) ∧ p.seqNum (sequenceAt r 1) = 2) ∨
      (p.seqNum (sequenceAt r 0) = 0 ∧ p.seqNum (sequenceAt r 1) ≤ 1 ∧
        1 ≤ p.tripNum (rankAt r 0) ∧ 1 ≤ p.tripNum (rankAt r 1) ∧
        1 ≤ p.tripNum (rankAt r 2)) ∨
      (p.seqNum (sequenceAt r 0) = 0 ∧ p.seqNum (sequenceAt r 1) = 2 ∧
        1 ≤ p.tripNum (rankAt r 0)) := by
  rw [← toHand_step, ← Placement.toHand_canonicalize (step p r),
    (Placement.canonic_canonicalize _).meldable_iff_tripNum_nonnegative,
    canonical_step_tripNum_nonnegative_iff h positive.2]
  have source := h (sequenceAt r 0)
  have next := h (sequenceAt r 1)
  have first := positive.2 (rankAt r 0)
  have second := positive.2 (rankAt r 1)
  have third := positive.2 (rankAt r 2)
  unfold borrow carry
  simp only [Pi.zero_apply] at first second third
  split_ifs <;> omega

/-- Only the first three affected triplet quotients can obstruct a rightward
step. Any meldable hand sharing that prefix certifies those quotients. -/
lemma meldable_right_of_prefix {p : Placement n} (h : p.Canonic) (positive : p.Nonnegative)
    (r : Start n) {d : VirtualHand n} (hd : Meldable d)
    (same : ∀ i : Rank n, i.val < r.val + 3 → right p.toHand r i = d i) :
    Meldable (right p.toHand r) := by
  have triplets := canonicalTriplet_prefix_eq (by have := r.isLt; omega) same
  rw [← toHand_step, ← Placement.toHand_canonicalize (step p r),
    (Placement.canonic_canonicalize _).meldable_iff_tripNum_nonnegative]
  intro i
  change 0 ≤ (step p r).canonicalize.tripNum i
  by_cases early : i.val < r.val + 3
  · have trace := (Placement.canonic_canonicalize (step p r)).canonicalTriplet_eq i
    rw [Placement.toHand_canonicalize, toHand_step, triplets i early] at trace
    rw [← trace]
    exact hd.canonicalTriplet_nonnegative i
  · rw [canonical_step_tripNum h]
    have original := positive.2 i
    have no_borrow : ¬(r.val ≤ i.val ∧ i.val ≤ r.val + 2) := by omega
    have nonnegative_carry : 0 ≤ carry p r := by unfold carry; split <;> norm_num
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sequenceAt_apply,
      Fin.val_zero, Fin.val_one, Nat.add_zero]
    split_ifs <;> simp_all
    all_goals omega

/-- The first step of any successful long rightward move is successful. The
congruence of the endpoints is a consequence, not an extra hypothesis here. -/
lemma meldable_right_of_long {c : VirtualHand n} (hc : Meldable c) (r : Start n)
    (j : Rank n) (far : r.val + 3 ≤ j.val)
    (hj : Meldable (moveTile c (rankAt r 0) j)) : Meldable (right c r) := by
  obtain ⟨p, ⟨positive, canonical, rfl⟩, _⟩ := hc.unique_canonical
  apply meldable_right_of_prefix canonical positive r hj
  intro i early
  have absent_step : i ≠ rankAt r 3 := by intro eq; subst i; simp at early
  have absent_end : i ≠ j := by intro eq; subst i; omega
  simp [right, moveTile, absent_step, absent_end]

end Moving
end Mahjong.VirtualHand
