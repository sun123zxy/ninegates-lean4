import Mathlib

namespace Mahjong

/--
Argurably we should consider `ℕ →₀ ℕ`, but its unfortunately uncomputable.
-/
def Hand (n : ℕ) := Fin (3 * n) → ℕ

namespace Hand

variable {n : ℕ}

instance : AddCommMonoid (Hand n) :=
  inferInstanceAs <| AddCommMonoid (Fin (3 * n) → ℕ)

@[simp]
lemma zero_apply (i : Fin (3 * n)) : (0 : Hand n) i = 0 := rfl

@[simp]
lemma add_apply (c d : Hand n) (i : Fin (3 * n)) : (c + d) i = c i + d i := rfl

@[simp]
lemma nsmul_apply (k : ℕ) (c : Hand n) (i : Fin (3 * n)) :
    (k • c) i = k • c i := rfl

def count (i : Fin (3 * n)) : Hand n →+ ℕ where
  toFun c := c i
  map_zero' := zero_apply i
  map_add' c d := add_apply c d i

@[simp]
lemma count_apply (i : Fin (3 * n)) (c : Hand n) : count i c = c i := rfl

@[ext]
lemma ext {c d : Hand n} (h : ∀ i, c i = d i) : c = d := by
  funext i
  exact h i

def size : Hand n →+ ℕ where
  toFun c := ∑ i, c i
  map_zero' := by simp
  map_add' c d := Finset.sum_add_distrib

def sum : Hand n →+ ℕ where
  toFun c := ∑ i, i * c i
  map_zero' := by simp
  map_add' c d := by
    simp only [add_apply, mul_add, Finset.sum_add_distrib]

def single (i : Fin (3 * n)) : Hand n :=
  fun j ↦ if j = i then 1 else 0

@[simp]
lemma single_apply (i j : Fin (3 * n)) : single i j = if j = i then 1 else 0 := rfl

@[simp]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  change (∑ j, if j = i then 1 else 0) = 1
  simp

@[simp]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by
  change (∑ j, j.val * if j = i then 1 else 0) = i.val
  simp

def pair (i : Fin (3 * n)) : Hand n :=
  2 • single i

@[simp]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by
  simp [pair]

@[simp]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by
  simp [pair]

def triplet (i : Fin (3 * n)) : Hand n :=
  3 • single i

@[simp]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by
  simp [triplet]

@[simp]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by
  simp [triplet]

def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[simp]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by
  simp [sequence]

@[simp]
lemma sum_sequence (i : Fin (3 * n - 2)) :
    sum (sequence i) = 3 * (i.val + 1) := by
  simp only [sequence, map_add, sum_single]
  omega

@[simp]
lemma sum_sequence_mod_three (i : Fin (3 * n - 2)) : sum (sequence i) % 3 = 0 := by
  rw [sum_sequence]
  exact Nat.mul_mod_right _ _

def Valid (c : Hand n) : Prop := ∀ i, c i ≤ 4

def Meldable (c : Hand n) : Prop :=
  ∃ (t : Fin (3 * n) → ℕ) (r : Fin (3 * n - 2) → ℕ),
  c = ∑ i, t i • triplet i + ∑ j, r j • sequence j

@[simp]
lemma Meldable.sequence {i : Fin (3 * n - 2)} : Meldable (sequence i) := by
  use 0, fun j ↦ if j = i then 1 else 0
  simp only [Pi.zero_apply, zero_nsmul, Finset.sum_const_zero, zero_add, ite_smul,
    one_nsmul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

@[simp]
lemma Meldable.triplet {i : Fin (3 * n)} : Meldable (triplet i) := by
  use fun j ↦ if j = i then 1 else 0, 0
  simp only [ite_smul, one_nsmul, zero_nsmul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Pi.zero_apply, Finset.sum_const_zero, add_zero]

lemma Meldable.add {c d : Hand n} (hc : Meldable c) (hd : Meldable d) :
    Meldable (c + d) := by
  obtain ⟨tc, rc, rfl⟩ := hc
  obtain ⟨td, rd, rfl⟩ := hd
  use tc + td, rc + rd
  simp only [Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
  ac_rfl

@[simp]
lemma Meldable.zero : Meldable (0 : Hand n) := by
  use 0, 0
  simp

lemma Meldable.nsmul {c : Hand n} (hc : Meldable c) (a : ℕ) :
    Meldable (a • c) := by
  induction a with
  | zero => simp
  | succ a ih => simpa only [succ_nsmul] using Meldable.add ih hc

lemma Meldable.finset_sum {ι : Type*} {s : Finset ι} {f : ι → Hand n}
    (hf : ∀ i ∈ s, Meldable (f i)) : Meldable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        Meldable.add (hf i (Finset.mem_insert_self i s))
          (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem Meldable.size_mod_three {c : Hand n} (hc : Meldable c) :
    size c % 3 = 0 := by
  obtain ⟨t, r, rfl⟩ := hc
  rw [map_add, map_sum, map_sum]
  simp only [map_nsmul, size_triplet, size_sequence, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

theorem Meldable.sum_mod_three {c : Hand n} (hc : Meldable c) :
    sum c % 3 = 0 := by
  obtain ⟨t, r, rfl⟩ := hc
  rw [map_add, map_sum, map_sum]
  simp only [map_nsmul, sum_triplet, sum_sequence, smul_eq_mul]
  simp_rw [mul_comm 3, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

def Winning (c : Hand n) : Prop :=
  Valid c ∧ ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + pair i

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  Winning (c + single i)

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + single i)

lemma IsWait.Valid (c : Hand n) (hc : IsWait c) : Valid c := by
  rcases hc with ⟨i, hi⟩
  intro j
  exact le_trans (Nat.le_add_right (c j) (single i j)) (hi.1 j)

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + single i)

end Hand

end Mahjong
