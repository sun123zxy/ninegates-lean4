import Mathlib

namespace Mahjong

/--
Argurably we should consider `ℕ →₀ ℕ`, but its unfortunately uncomputable.
-/
structure Hand (n : ℕ) where
  toFun : Fin (3 * n) → ℕ

namespace Hand

variable {n : ℕ}

instance : FunLike (Hand n) (Fin (3 * n)) ℕ where
  coe := Hand.toFun
  coe_injective := by
    intro c d h
    cases c
    cases d
    congr

@[ext, grind ext]
lemma ext {c d : Hand n} (h : ∀ i, c i = d i) : c = d :=
  DFunLike.ext c d h

@[simp, grind =]
lemma mk_apply (f : Fin (3 * n) → ℕ) (i : Fin (3 * n)) :
    Hand.mk f i = f i := rfl

instance : Zero (Hand n) := ⟨⟨0⟩⟩

instance : Add (Hand n) :=
  ⟨fun c d ↦ ⟨fun i ↦ c i + d i⟩⟩

instance : SMul ℕ (Hand n) :=
  ⟨fun k c ↦ ⟨fun i ↦ k • c i⟩⟩

instance : IsZeroApply (Hand n) (Fin (3 * n)) ℕ where
  zero_apply _ := rfl

instance : IsAddApply (Hand n) (Fin (3 * n)) ℕ where
  add_apply _ _ _ := rfl

instance : IsSMulApply ℕ (Hand n) (Fin (3 * n)) ℕ where
  smul_apply _ _ _ := rfl

instance : AddCommMonoid (Hand n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc := by intros; grind
  zero_add := by intros; grind
  add_zero := by intros; grind
  add_comm := by intros; grind
  nsmul_zero := by intros; grind
  nsmul_succ := by intros; grind

def size : Hand n →+ ℕ where
  toFun c := ∑ i, c i
  map_zero' := by simp
  map_add' c d := by
    simpa only [add_apply] using
      Finset.sum_add_distrib (f := fun i ↦ c i) (g := fun i ↦ d i)

def sum : Hand n →+ ℕ where
  toFun c := ∑ i, i * c i
  map_zero' := by simp
  map_add' _ _ := by
    simp only [add_apply, mul_add, Finset.sum_add_distrib]

@[grind =]
def single (i : Fin (3 * n)) : Hand n :=
  ⟨fun j ↦ if j = i then 1 else 0⟩

@[simp, grind =]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  simp [size, single]

@[simp, grind =]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by
  simp [sum, single]

@[grind =]
def pair (i : Fin (3 * n)) : Hand n :=
  2 • single i

@[simp, grind =]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by
  simp [pair]

@[simp, grind =]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by
  simp [pair]

@[grind =]
def triplet (i : Fin (3 * n)) : Hand n :=
  3 • single i

@[simp, grind =]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by
  simp [triplet]

@[simp, grind =]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by
  simp [triplet]

@[grind =]
def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[simp, grind =]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by
  grind [sequence]

@[simp, grind =]
lemma sum_sequence (i : Fin (3 * n - 2)) :
    sum (sequence i) = 3 * (i.val + 1) := by
  grind [sequence]

def Valid (c : Hand n) : Prop := ∀ i, c i ≤ 4

namespace Meldable

@[ext]
structure Placement (n : ℕ) where
  tripNum : Fin (3 * n) → ℕ
  seqNum : Fin (3 * n - 2) → ℕ

attribute [grind ext] Placement.ext

namespace Placement

instance : AddCommMonoid (Placement n) where
  zero := ⟨0, 0⟩
  add p q := ⟨p.tripNum + q.tripNum, p.seqNum + q.seqNum⟩
  nsmul k p := ⟨k • p.tripNum, k • p.seqNum⟩
  add_assoc p q r := by
    ext i <;> exact add_assoc _ _ _
  zero_add p := by
    ext i <;> exact zero_add _
  add_zero p := by
    ext i <;> exact add_zero _
  add_comm p q := by
    ext i <;> exact add_comm _ _
  nsmul_zero p := by
    ext i <;> exact zero_nsmul _
  nsmul_succ k p := by
    ext i <;> exact succ_nsmul _ _

@[simp, grind =]
lemma tripNum_zero (i : Fin (3 * n)) : (0 : Placement n).tripNum i = 0 := rfl

@[simp, grind =]
lemma seqNum_zero (i : Fin (3 * n - 2)) : (0 : Placement n).seqNum i = 0 := rfl

@[simp, grind =]
lemma tripNum_add (p q : Placement n) (i : Fin (3 * n)) :
    (p + q).tripNum i = p.tripNum i + q.tripNum i := rfl

@[simp, grind =]
lemma seqNum_add (p q : Placement n) (i : Fin (3 * n - 2)) :
    (p + q).seqNum i = p.seqNum i + q.seqNum i := rfl

@[simp, grind =]
lemma tripNum_nsmul (k : ℕ) (p : Placement n) (i : Fin (3 * n)) :
    (k • p).tripNum i = k • p.tripNum i := rfl

@[simp, grind =]
lemma seqNum_nsmul (k : ℕ) (p : Placement n) (i : Fin (3 * n - 2)) :
    (k • p).seqNum i = k • p.seqNum i := rfl

@[grind =]
def toHand : Placement n →+ Hand n where
  toFun p :=
    ∑ i, p.tripNum i • triplet i + ∑ j, p.seqNum j • sequence j
  map_zero' := by simp
  map_add' p q := by
    simp only [tripNum_add, seqNum_add, add_nsmul, Finset.sum_add_distrib]
    ac_rfl

@[grind =]
lemma toHand_eq_sum (p : Placement n) :
    p.toHand =
      ∑ i, p.tripNum i • Hand.triplet i +
        ∑ j, p.seqNum j • Hand.sequence j := rfl

@[grind =]
lemma toHand_apply (p : Placement n) (k : Fin (3 * n)) :
    p.toHand k =
      ∑ i, (p.tripNum i • Hand.triplet i) k +
        ∑ j, (p.seqNum j • Hand.sequence j) k := by
  simp [toHand_eq_sum]

end Placement

def IsWitness (p : Meldable.Placement n) (c : Hand n) : Prop :=
  p.toHand = c

@[grind ←]
lemma IsWitness.add {p q : Meldable.Placement n} {c d : Hand n}
    (hp : IsWitness p c) (hq : IsWitness q d) :
    IsWitness (p + q) (c + d) := by
  grind [IsWitness]

@[simp]
lemma IsWitness.zero :
    IsWitness (0 : Meldable.Placement n) (0 : Hand n) := by
  simp [IsWitness]

@[grind ←]
lemma IsWitness.nsmul {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : ℕ) : IsWitness (k • p) (k • c) := by
  grind [IsWitness]

end Meldable

def Meldable (c : Hand n) : Prop :=
  ∃ p : Meldable.Placement n, Meldable.IsWitness p c

namespace Meldable

@[simp]
lemma sequence {i : Fin (3 * n - 2)} : Meldable (sequence i) := by
  refine ⟨⟨0, fun j ↦ if j = i then 1 else 0⟩, ?_⟩
  simp [IsWitness, Meldable.Placement.toHand]

@[simp]
lemma triplet {i : Fin (3 * n)} : Meldable (triplet i) := by
  refine ⟨⟨fun j ↦ if j = i then 1 else 0, 0⟩, ?_⟩
  simp [IsWitness, Meldable.Placement.toHand]

@[grind ←]
lemma add {c d : Hand n} (hc : Meldable c) (hd : Meldable d) :
    Meldable (c + d) := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := hd
  exact ⟨p + q, hp.add hq⟩

@[simp]
lemma zero : Meldable (0 : Hand n) := by
  exact ⟨0, IsWitness.zero⟩

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

@[grind →]
theorem size_mod_three {c : Hand n} (hc : Meldable c) :
    size c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Meldable.Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, size_triplet, size_sequence, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

@[grind →]
theorem sum_mod_three {c : Hand n} (hc : Meldable c) :
    sum c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Meldable.Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, sum_triplet, sum_sequence, smul_eq_mul]
  simp_rw [mul_comm 3, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

end Meldable

def Winning (c : Hand n) : Prop :=
  Valid c ∧ size c = 3 * n + 5 ∧
    ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + pair i

@[grind →]
lemma Winning.size {c : Hand n} (hc : Winning c) : size c = 3 * n + 5 :=
  hc.2.1

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  Winning (c + single i)

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + single i)

@[grind →]
lemma IsWait.Valid (c : Hand n) (hc : IsWait c) : Valid c := by
  rcases hc with ⟨i, hi⟩
  intro j
  exact le_trans (Nat.le_add_right (c j) (single i j)) (hi.1 j)

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + single i)

@[grind →]
lemma IsFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    size c = 3 * n + 4 := by
  let i : Fin (3 * n) := ⟨0, by omega⟩
  have hsize := (hc i).size
  simp only [map_add, size_single] at hsize
  omega

end Hand

end Mahjong
