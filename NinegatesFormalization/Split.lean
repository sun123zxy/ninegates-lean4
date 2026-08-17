import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ}

def restrictLT (k : ℤ) : Hand n →+ Hand n := filter (· < k)

def restrictGT (k : ℤ) : Hand n →+ Hand n := filter (k < ·)

@[simp, grind =]
theorem restrictLT_apply (k : ℤ) (c : Hand n) (i : ℤ) :
    restrictLT k c i = if i < k then c i else 0 := by
  simp [restrictLT]

@[simp, grind =]
theorem restrictGT_apply (k : ℤ) (c : Hand n) (i : ℤ) :
    restrictGT k c i = if k < i then c i else 0 := by
  simp [restrictGT]

namespace Meldable.Placement

def restrictLT (k : ℤ) : Placement n →+ Placement n :=
  filter (· < k) (fun i ↦ i + 2 < k)

def restrictGT (k : ℤ) : Placement n →+ Placement n :=
  filter (k < ·) (k < ·)

@[simp, grind =]
theorem tripNum_restrictLT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictLT k p).tripNum i = if i < k then p.tripNum i else 0 := by
  simp [restrictLT]

@[simp, grind =]
theorem seqNum_restrictLT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictLT k p).seqNum i = if i + 2 < k then p.seqNum i else 0 := by
  simp [restrictLT]

@[simp, grind =]
theorem tripNum_restrictGT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictGT k p).tripNum i = if k < i then p.tripNum i else 0 := by
  simp [restrictGT]

@[simp, grind =]
theorem seqNum_restrictGT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictGT k p).seqNum i = if k < i then p.seqNum i else 0 := by
  simp [restrictGT]

end Meldable.Placement

@[simp, grind =]
theorem restrictLT_single_of_lt (k : ℤ) (i : Fin (3 * n)) (hi : i.val < k) :
    restrictLT k (single i) = single i := by
  apply Hand.ext
  grind

@[simp, grind =]
theorem restrictLT_single_of_not_lt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬(i.val : ℤ) < k) :
    restrictLT k (single i) = 0 := by
  apply Hand.ext
  grind

@[simp, grind =]
theorem restrictGT_single_of_gt (k : ℤ) (i : Fin (3 * n)) (hi : k < i.val) :
    restrictGT k (single i) = single i := by
  apply Hand.ext
  grind

@[simp, grind =]
theorem restrictGT_single_of_not_gt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬k < (i.val : ℤ)) :
    restrictGT k (single i) = 0 := by
  apply Hand.ext
  grind

@[simp, grind =]
theorem restrictLT_pair_of_lt (k : ℤ) (i : Fin (3 * n)) (hi : i.val < k) :
    restrictLT k (pair i) = pair i := by simp [pair, hi]

@[simp, grind =]
theorem restrictLT_pair_of_not_lt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬(i.val : ℤ) < k) :
    restrictLT k (pair i) = 0 := by simp [pair, hi]

@[simp, grind =]
theorem restrictGT_pair_of_gt (k : ℤ) (i : Fin (3 * n)) (hi : k < i.val) :
    restrictGT k (pair i) = pair i := by simp [pair, hi]

@[simp, grind =]
theorem restrictGT_pair_of_not_gt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬k < (i.val : ℤ)) :
    restrictGT k (pair i) = 0 := by simp [pair, hi]

@[grind →]
theorem Meldable.IsWitness.split_at_zero {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : ℤ) (hk : c k = 0) :
    IsWitness (Meldable.Placement.restrictLT k p) (restrictLT k c) ∧
      IsWitness (Meldable.Placement.restrictGT k p) (restrictGT k c) := by
  constructor <;> unfold IsWitness <;> apply Hand.ext <;> intro i
  all_goals
    grind only [IsWitness, Meldable.Placement.toHand_apply,
      Meldable.Placement.tripNum_restrictLT, Meldable.Placement.seqNum_restrictLT,
      Meldable.Placement.tripNum_restrictGT, Meldable.Placement.seqNum_restrictGT,
      restrictLT_apply, restrictGT_apply]

@[grind →]
theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : ℤ) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  grind [Meldable]

end Mahjong.Hand
