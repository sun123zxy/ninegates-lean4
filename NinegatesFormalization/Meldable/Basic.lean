import NinegatesFormalization.Basic

/-!
# Meld decompositions

## Main Definitions

- `Meldable.Placement n` is a specification of a placement of melds.

  - `tripNum i` counts triplets at `i`,
  - `seqNum i` counts sequences starting at `i`.

  Both observations are zero-extended to integer coordinates.

- For a placement `p`, `p.toHand` is the hand given by
  the sum of the triplets and sequences specified by `p`.

- A placement `p` is a witness for a hand `c` if `c` is given by `p`.
  This defines `Meldable.IsWitness p c`.

- A hand is `Meldable` if it has a witness.
-/

namespace Mahjong.Hand

open Mahjong.Internal

variable {n : ℕ}

namespace Meldable

structure Placement (n : ℕ) where
  private mk ::
  private tripNum' : Fin (3 * n) → ℕ
  private seqNum' : Fin (3 * n - 2) → ℕ

namespace Placement

def ofFn (tripNum : Fin (3 * n) → ℕ) (seqNum : Fin (3 * n - 2) → ℕ) :
    Placement n := .mk tripNum seqNum

private lemma ext_raw {p q : Placement n}
    (htrip : ∀ i, p.tripNum' i = q.tripNum' i)
    (hseq : ∀ i, p.seqNum' i = q.seqNum' i) : p = q := by
  cases p; cases q
  congr <;> grind

instance : Zero (Placement n) := ⟨ofFn 0 0⟩

instance : Add (Placement n) :=
  ⟨fun p q ↦ ofFn (p.tripNum' + q.tripNum') (p.seqNum' + q.seqNum')⟩

instance : SMul ℕ (Placement n) :=
  ⟨fun k p ↦ ofFn (k • p.tripNum') (k • p.seqNum')⟩

instance : AddCommMonoid (Placement n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc p q r := by apply ext_raw <;> intro i <;> exact add_assoc _ _ _
  zero_add p := by apply ext_raw <;> intro i <;> exact zero_add _
  add_zero p := by apply ext_raw <;> intro i <;> exact add_zero _
  add_comm p q := by apply ext_raw <;> intro i <;> exact add_comm _ _
  nsmul_zero k := by apply ext_raw <;> intro i <;> exact Nat.zero_mul _
  nsmul_succ k p := by apply ext_raw <;> intro i <;> exact Nat.succ_mul k _

def tripNum : Placement n →+ (ℤ → ℕ) where
  toFun p := extend p.tripNum'
  map_zero' := by
    funext i
    change extend (0 : Fin (3 * n) → ℕ) i = 0
    exact extend_zero i
  map_add' p q := by
    funext i
    change extend (p.tripNum' + q.tripNum') i =
      extend p.tripNum' i + extend q.tripNum' i
    exact extend_add _ _ _

def seqNum : Placement n →+ (ℤ → ℕ) where
  toFun p := extend p.seqNum'
  map_zero' := by
    funext i
    change extend (0 : Fin (3 * n - 2) → ℕ) i = 0
    exact extend_zero i
  map_add' p q := by
    funext i
    change extend (p.seqNum' + q.seqNum') i =
      extend p.seqNum' i + extend q.seqNum' i
    exact extend_add _ _ _

@[grind =]
lemma tripNum_ofFn (trip : Fin (3 * n) → ℕ) (seq : Fin (3 * n - 2) → ℕ)
    (i : ℤ) :
    (ofFn trip seq).tripNum i =
      if h : 0 ≤ i ∧ i < 3 * n then trip ⟨i.toNat, by omega⟩ else 0 := by
  rfl

@[simp 1100, grind =]
private lemma tripNum_ofFn_fin
    (trip : Fin (3 * n) → ℕ) (seq : Fin (3 * n - 2) → ℕ)
    (i : Fin (3 * n)) : (ofFn trip seq).tripNum i.val = trip i :=
  extend_coe _ _

@[grind =]
lemma seqNum_ofFn (trip : Fin (3 * n) → ℕ) (seq : Fin (3 * n - 2) → ℕ)
    (i : ℤ) :
    (ofFn trip seq).seqNum i =
      if h : 0 ≤ i ∧ i < ((3 * n - 2 : ℕ) : ℤ) then
        seq ⟨i.toNat, by omega⟩ else 0 := by
  rfl

@[simp 1100, grind =]
private lemma seqNum_ofFn_fin
    (trip : Fin (3 * n) → ℕ) (seq : Fin (3 * n - 2) → ℕ)
    (i : Fin (3 * n - 2)) : (ofFn trip seq).seqNum i.val = seq i :=
  extend_coe _ _

@[simp, grind =]
lemma tripNum_of_lt_zero (p : Placement n) (i : ℤ) (hi : i < 0) :
    p.tripNum i = 0 :=
  extend_of_lt_zero _ _ hi

@[simp, grind =]
lemma tripNum_of_ge (p : Placement n) (i : ℤ) (hi : 3 * n ≤ i) :
    p.tripNum i = 0 :=
  extend_of_ge _ _ hi

@[simp, grind =]
lemma seqNum_of_lt_zero (p : Placement n) (i : ℤ) (hi : i < 0) :
    p.seqNum i = 0 :=
  extend_of_lt_zero _ _ hi

@[simp, grind =]
lemma seqNum_of_ge (p : Placement n) (i : ℤ) (hi : (3 * n - 2 : ℕ) ≤ i) :
    p.seqNum i = 0 :=
  extend_of_ge _ _ hi

@[ext, grind ext]
lemma ext {p q : Placement n}
    (htrip : ∀ i : ℤ, 0 ≤ i → i < 3 * n → p.tripNum i = q.tripNum i)
    (hseq : ∀ i : ℤ, 0 ≤ i → i < (3 * n - 2 : ℕ) → p.seqNum i = q.seqNum i) : p = q := by
  apply ext_raw
  · intro i
    simpa [tripNum] using htrip i.val (by omega) (by omega)
  · intro i
    simpa [seqNum] using hseq i.val (by omega) (by omega)

def toHand : Placement n →+ Hand n where
  toFun p :=
    ∑ i, p.tripNum i.val • Hand.triplet i +
      ∑ j, p.seqNum j.val • Hand.sequence j
  map_zero' := by simp
  map_add' _ _ := by simp [add_nsmul, Finset.sum_add_distrib]; ac_rfl

lemma toHand_eq_sum (p : Placement n) :
    p.toHand =
      ∑ i, p.tripNum i.val • Hand.triplet i +
        ∑ j, p.seqNum j.val • Hand.sequence j := rfl

@[simp, grind =]
lemma toHand_apply (p : Placement n) (i : ℤ) :
    p.toHand i =
      3 * p.tripNum i + p.seqNum i + p.seqNum (i - 1) + p.seqNum (i - 2) := by
  have htrip :
      (∑ j : Fin (3 * n), if i = (j.val : ℤ) then p.tripNum j.val * 3 else 0) =
        p.tripNum i * 3 := by
    simpa [tripNum, mul_comm] using sum_ite_eq_extend 3 p.tripNum' i 0
  have hseq (d : ℕ) :
      (∑ j : Fin (3 * n - 2),
        if i = (j.val : ℤ) + d then p.seqNum j.val else 0) =
        p.seqNum (i - d) := by
    simpa [seqNum] using sum_ite_eq_extend 1 p.seqNum' i d
  have hseq₀ := hseq 0
  have hseq₁ := hseq 1
  have hseq₂ := hseq 2
  norm_num at hseq₀ hseq₁ hseq₂
  simp [toHand, Hand.triplet, Hand.sequence, Hand.single_apply,
    Finset.sum_add_distrib]
  simp only [htrip, hseq₀, hseq₁, hseq₂]
  omega

end Placement

def IsWitness (p : Meldable.Placement n) (c : Hand n) : Prop := p.toHand = c

@[grind ←]
lemma IsWitness.add {p q : Meldable.Placement n} {c d : Hand n}
    (hp : IsWitness p c) (hq : IsWitness q d) :
    IsWitness (p + q) (c + d) := by
  grind [IsWitness]

@[simp]
lemma IsWitness.zero : IsWitness (0 : Meldable.Placement n) (0 : Hand n) := by simp [IsWitness]

@[grind ←]
lemma IsWitness.nsmul {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : ℕ) : IsWitness (k • p) (k • c) := by
  grind [IsWitness]

end Meldable

def Meldable (c : Hand n) : Prop := ∃ p : Meldable.Placement n, Meldable.IsWitness p c

namespace Meldable

@[simp]
lemma sequence {i : Fin (3 * n - 2)} : Meldable (sequence i) := by
  refine ⟨Placement.ofFn 0 (fun j ↦ if j = i then 1 else 0), ?_⟩
  simp [IsWitness, Placement.toHand_eq_sum]

@[simp]
lemma triplet {i : Fin (3 * n)} : Meldable (triplet i) := by
  refine ⟨Placement.ofFn (fun j ↦ if j = i then 1 else 0) 0, ?_⟩
  simp [IsWitness, Placement.toHand_eq_sum]

@[grind ←]
lemma add {c d : Hand n} (hc : Meldable c) (hd : Meldable d) :
    Meldable (c + d) := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := hd
  exact ⟨p + q, hp.add hq⟩

@[simp]
lemma zero : Meldable (0 : Hand n) := ⟨0, IsWitness.zero⟩

@[grind ←]
lemma nsmul {c : Hand n} (hc : Meldable c) (a : ℕ) :
    Meldable (a • c) := by
  obtain ⟨p, hp⟩ := hc
  exact ⟨a • p, hp.nsmul a⟩

lemma finset_sum {ι : Type*} {s : Finset ι} {f : ι → Hand n}
    (hf : ∀ i ∈ s, Meldable (f i)) : Meldable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        Meldable.add (hf i (Finset.mem_insert_self i s))
          (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem size_mod_three {c : Hand n} (hc : Meldable c) :
    size c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, size_triplet, size_sequence, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

theorem sum_mod_three {c : Hand n} (hc : Meldable c) :
    sum c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, sum_triplet, sum_sequence, smul_eq_mul]
  simp_rw [mul_comm 3, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

end Meldable

end Mahjong.Hand
