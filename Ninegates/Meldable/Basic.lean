import Ninegates.Basic

/-!
# Meld decompositions

## Main definitions

- `Placement n` records triplet and sequence multiplicities on the finite tile
  coordinates. Sequence multiplicities at the final two coordinates are required
  to be zero.

- For a placement `p`, `p.toHand` is the hand given by the finite sum of the
  triplets and sequences specified by `p`.

- A placement is a witness for a hand when its `toHand` is that hand. A hand is
  `Meldable` when it has such a witness.

## Design notes

### `Placement.toHand_apply` automation

`seqNum` requires a case split on the first two coordinates.
We design `toHand_apply` automation as follows:

- `toHand_apply` is a `@[grind =]` lemma whose statement contains `if`.
  Recall that `grind` is designed to handle case splits, so this lemma
  is useful for downstream when they do not bother with the case split,
  or has a case split that is not in the exact form where `toHand_apply` specifies.

- `toHand_apply_of_eq_zero`, `toHand_apply_of_eq_one`, and
  `toHand_apply_of_ge_two` are `@[simp]` lemmas for each specific case.
  These reductions are safe as no `if` case splits remain in the statement.

  Note that we choose not to `@[grind]` them, because if we do,
  when `grind` matches a `p.toHand i`, it immediately put multiple implications,
  e.g. `i.val = 0 → p.toHand i = 3 * p.tripNum i + p.seqNum i`, into the whiteboard,
  which is unnecessary as the `if`-lemma with `@[grind]` will handles the case split,
  and `grind` is designed to handle case splits effectively.

The effectiveness of this design is verified by the neat proof of
`IsLiveFullWait.standardLiveFullWait`.
-/

namespace Mahjong.Hand

variable {n : ℕ}

namespace Meldable

@[ext]
structure Placement (n : ℕ) where
  tripNum : Fin (3 * n) → ℕ
  seqNum : Fin (3 * n) → ℕ
  seqNum_tail :
    (∀ i, i.val + 2 = 3 * n → seqNum i = 0) ∧
    (∀ i, i.val + 1 = 3 * n → seqNum i = 0)
deriving Repr

attribute [grind ext] Placement.ext

namespace Placement

instance : Zero (Placement n) :=
  ⟨⟨0, 0, by simp⟩⟩

instance : Add (Placement n) :=
  ⟨fun p q ↦ ⟨p.tripNum + q.tripNum, p.seqNum + q.seqNum, by
    constructor
    · intro i hi
      simp [p.seqNum_tail.1 i hi, q.seqNum_tail.1 i hi]
    · intro i hi
      simp [p.seqNum_tail.2 i hi, q.seqNum_tail.2 i hi]⟩⟩

instance : SMul ℕ (Placement n) :=
  ⟨fun k p ↦ ⟨k • p.tripNum, k • p.seqNum, by
    constructor
    · intro i hi
      simp [p.seqNum_tail.1 i hi]
    · intro i hi
      simp [p.seqNum_tail.2 i hi]⟩⟩

@[simp, grind =]
lemma tripNum_zero (i : Fin (3 * n)) : (0 : Placement n).tripNum i = 0 := rfl

@[simp, grind =]
lemma seqNum_zero (i : Fin (3 * n)) : (0 : Placement n).seqNum i = 0 := rfl

@[simp, grind =]
lemma tripNum_add (p q : Placement n) (i : Fin (3 * n)) :
    (p + q).tripNum i = p.tripNum i + q.tripNum i := rfl

@[simp, grind =]
lemma seqNum_add (p q : Placement n) (i : Fin (3 * n)) :
    (p + q).seqNum i = p.seqNum i + q.seqNum i := rfl

@[simp, grind =]
lemma tripNum_nsmul (k : ℕ) (p : Placement n) (i : Fin (3 * n)) :
    (k • p).tripNum i = k * p.tripNum i := rfl

@[simp, grind =]
lemma seqNum_nsmul (k : ℕ) (p : Placement n) (i : Fin (3 * n)) :
    (k • p).seqNum i = k * p.seqNum i := rfl

instance : AddCommMonoid (Placement n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc p q r := by ext i <;> simp [add_assoc]
  zero_add p := by ext i <;> simp
  add_zero p := by ext i <;> simp
  add_comm p q := by ext i <;> simp [add_comm]
  nsmul_zero k := by ext i <;> simp
  nsmul_succ k p := by ext i <;> simp [Nat.succ_mul, add_comm]

@[simp, grind =]
lemma seqNum_of_ge (p : Placement n) (i : Fin (3 * n))
    (hi : 3 * n - 2 ≤ i.val) : p.seqNum i = 0 := by
  rcases p.seqNum_tail with ⟨hlast₂, hlast⟩
  by_cases h : i.val + 1 = 3 * n
  · exact hlast i h
  · apply hlast₂ i
    omega

def toHand : Placement n →+ Hand n where
  toFun p :=
    ∑ i, p.tripNum i • Hand.triplet i +
      ∑ j, p.seqNum ⟨j.val, by omega⟩ • Hand.sequence j
  map_zero' := by simp
  map_add' _ _ := by simp [add_nsmul, Finset.sum_add_distrib]; ac_rfl

lemma toHand_eq_sum (p : Placement n) :
    p.toHand =
      ∑ i, p.tripNum i • Hand.triplet i +
        ∑ j, p.seqNum ⟨j.val, by omega⟩ • Hand.sequence j := rfl

lemma seq_sum (p : Placement n) (i : Fin (3 * n)) (d : ℕ)
    (hd₂ : d ≤ 2) :
    (∑ j : Fin (3 * n - 2),
      if i.val = j.val + d then p.seqNum ⟨j.val, by omega⟩ else 0) =
      if hd : d ≤ i.val then p.seqNum ⟨i.val - d, by omega⟩ else 0 := by
  classical
  split
  · rename_i hd
    by_cases hi : i.val - d < 3 * n - 2
    · let j : Fin (3 * n - 2) := ⟨i.val - d, hi⟩
      rw [Finset.sum_eq_single j] <;> grind [Fin.ext_iff]
    · have hge : 3 * n - 2 ≤ i.val - d := by omega
      rw [seqNum_of_ge p ⟨i.val - d, by omega⟩ hge]
      apply Finset.sum_eq_zero
      grind
  · rename_i hd
    apply Finset.sum_eq_zero
    grind

@[grind =]
lemma toHand_apply (p : Placement n) (i : Fin (3 * n)) :
    p.toHand i =
      if h₀ : i.val = 0 then
        3 * p.tripNum i + p.seqNum i
      else if h₁ : i.val = 1 then
        3 * p.tripNum i + p.seqNum i + p.seqNum ⟨0, by omega⟩
      else
        3 * p.tripNum i + p.seqNum i +
          p.seqNum ⟨i.val - 1, by omega⟩ + p.seqNum ⟨i.val - 2, by omega⟩ := by
  simp only [toHand, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_apply, sum_apply,
    smul_apply, Hand.triplet_apply, smul_eq_mul, mul_ite, mul_zero,
    Hand.sequence_apply, mul_one, dite_eq_ite]
  have hsum :
      (∑ j : Fin (3 * n - 2),
        if i.val = j.val ∨ i.val = j.val + 1 ∨
            i.val = j.val + 2
          then p.seqNum ⟨j.val, by omega⟩ else 0) =
        (∑ j : Fin (3 * n - 2),
          if i.val = j.val then p.seqNum ⟨j.val, by omega⟩ else 0) +
        (∑ j : Fin (3 * n - 2),
          if i.val = j.val + 1 then p.seqNum ⟨j.val, by omega⟩ else 0) +
        ∑ j : Fin (3 * n - 2),
          if i.val = j.val + 2 then p.seqNum ⟨j.val, by omega⟩ else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    grind
  rw [hsum]
  have htrip :
      (∑ j : Fin (3 * n), if i.val = j.val then p.tripNum j * 3 else 0) =
        3 * p.tripNum i := by
    rw [Finset.sum_eq_single i] <;> grind [Fin.ext_iff]
  rw [htrip]
  have h0 :
      (∑ j : Fin (3 * n - 2),
        if i.val = j.val then p.seqNum ⟨j.val, by omega⟩ else 0) = p.seqNum i := by
    simpa using seq_sum p i 0 (by omega)
  rw [h0, seq_sum p i 1 (by omega), seq_sum p i 2 (by omega)]
  by_cases hi₀ : i.val = 0 <;> by_cases hi₁ : i.val = 1 <;> grind

@[simp, grind =]
lemma toHand_apply_of_eq_zero (p : Placement n) (i : Fin (3 * n))
    (hi : i.val = 0) :
    p.toHand i = 3 * p.tripNum i + p.seqNum i := by grind

@[simp]
lemma toHand_apply_of_eq_one (p : Placement n) (i : Fin (3 * n))
    (hi : i.val = 1) :
    p.toHand i = 3 * p.tripNum i + p.seqNum i +
      p.seqNum ⟨0, by omega⟩ := by grind

@[simp]
lemma toHand_apply_of_ge_two (p : Placement n) (i : Fin (3 * n))
    (hi : 2 ≤ i.val) :
    p.toHand i = 3 * p.tripNum i + p.seqNum i +
      p.seqNum ⟨i.val - 1, by omega⟩ + p.seqNum ⟨i.val - 2, by omega⟩ := by grind

end Placement

@[grind =]
def IsWitness (p : Placement n) (c : Hand n) : Prop := p.toHand = c

@[grind ←]
lemma IsWitness.add {p q : Placement n} {c d : Hand n}
    (hp : IsWitness p c) (hq : IsWitness q d) :
    IsWitness (p + q) (c + d) := by
  grind [IsWitness]

@[simp]
lemma IsWitness.zero : IsWitness (0 : Placement n) (0 : Hand n) := by simp [IsWitness]

@[grind ←]
lemma IsWitness.nsmul {p : Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : ℕ) : IsWitness (k • p) (k • c) := by
  grind [IsWitness]

end Meldable

def Meldable (c : Hand n) : Prop := ∃ p : Meldable.Placement n, Meldable.IsWitness p c

namespace Meldable

@[simp]
lemma sequence {i : Fin (3 * n - 2)} : Meldable (sequence i) := by
  refine ⟨⟨0, fun j ↦ if j.val = i.val then 1 else 0, ?_⟩, ?_⟩
  · constructor <;> grind
  · simp only [IsWitness, Placement.toHand_eq_sum, Pi.zero_apply, zero_nsmul,
      Finset.sum_const_zero, zero_add, ite_smul, one_nsmul]
    rw [Finset.sum_eq_single i] <;> grind [Fin.ext_iff]

@[simp]
lemma triplet {i : Fin (3 * n)} : Meldable (triplet i) := by
  refine ⟨⟨fun j ↦ if j = i then 1 else 0, 0, by simp⟩, ?_⟩
  · simp [IsWitness, Placement.toHand_eq_sum]

@[grind ←]
lemma add {c d : Hand n} (hc : Meldable c) (hd : Meldable d) : Meldable (c + d) := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := hd
  exact ⟨p + q, hp.add hq⟩

@[simp]
lemma zero : Meldable (0 : Hand n) := ⟨0, IsWitness.zero⟩

@[grind ←]
lemma nsmul {c : Hand n} (hc : Meldable c) (a : ℕ) : Meldable (a • c) := by
  obtain ⟨p, hp⟩ := hc
  exact ⟨a • p, hp.nsmul a⟩

theorem size_mod_three {c : Hand n} (hc : Meldable c) : size c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, size_triplet, size_sequence, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

theorem sum_mod_three {c : Hand n} (hc : Meldable c) : sum c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, sum_triplet, sum_sequence, smul_eq_mul]
  simp_rw [mul_comm 3, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

end Meldable

end Mahjong.Hand
