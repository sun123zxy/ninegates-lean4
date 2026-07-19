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

@[ext]
lemma ext {c d : Hand n} (h : ∀ i, c i = d i) : c = d := by
  funext i
  exact h i

def size (c : Hand n) := ∑ i, c i

@[simp]
lemma size_zero : size (0 : Hand n) = 0 := by
  simp [size]

lemma size_add (c d : Hand n) : size (c + d) = size c + size d := by
  exact Finset.sum_add_distrib

def sizeHom : Hand n →+ ℕ where
  toFun := size
  map_zero' := size_zero
  map_add' := size_add

@[simp]
lemma sizeHom_apply (c : Hand n) : sizeHom c = size c := rfl

lemma size_nsmul (k : ℕ) (c : Hand n) : size (k • c) = k • size c := by
  repeat rw [← sizeHom_apply]
  apply map_nsmul

def sum (c : Hand n) := ∑ i, i * c i

@[simp]
lemma sum_zero : sum (0 : Hand n) = 0 := by
  simp [sum]

lemma sum_add (c d : Hand n) : sum (c + d) = sum c + sum d := by
  simp only [sum, add_apply, ← Finset.sum_add_distrib]
  congr; funext; rw [mul_add]

def sumHom : Hand n →+ ℕ where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
lemma sumHom_apply (c : Hand n) : sumHom c = sum c := rfl

lemma sum_nsmul (k : ℕ) (c : Hand n) : sum (k • c) = k • sum c := by
  repeat rw [← sumHom_apply]
  apply map_nsmul

def single (i : Fin (3 * n)) : Hand n :=
  fun j ↦ if j = i then 1 else 0

@[simp]
lemma single_apply (i j : Fin (3 * n)) : single i j = if j = i then 1 else 0 := rfl

@[simp]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  simp [size]

@[simp]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by
  simp [sum]

def pair (i : Fin (3 * n)) : Hand n :=
  2 • single i

@[simp]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by
  simp [pair, size_nsmul]

@[simp]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by
  simp [pair, sum_nsmul]

def triplet (i : Fin (3 * n)) : Hand n :=
  3 • single i

@[simp]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by
  simp [triplet, size_nsmul]

@[simp]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by
  simp [triplet, sum_nsmul]

def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[simp]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by
  simp [sequence, size_add]

@[simp]
lemma sum_sequence (i : Fin (3 * n - 2)) :
    sum (sequence i) = 3 * (i.val + 1) := by
  simp only [sequence, sum_add, sum_single]
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
  rw [← sizeHom_apply, map_add, map_sum, map_sum]
  simp only [map_nsmul, sizeHom_apply, size_triplet, size_sequence, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

theorem Meldable.sum_mod_three {c : Hand n} (hc : Meldable c) :
    sum c % 3 = 0 := by
  obtain ⟨t, r, rfl⟩ := hc
  rw [← sumHom_apply, map_add, map_sum, map_sum]
  simp only [map_nsmul, sumHom_apply, sum_triplet, sum_sequence, smul_eq_mul]
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
