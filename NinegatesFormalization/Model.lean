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

@[simp]
lemma size_add (c d : Hand n) : size (c + d) = size c + size d := by
  change (∑ i, (c i + d i)) = (∑ i, c i) + (∑ i, d i)
  exact Finset.sum_add_distrib

@[simp]
lemma size_nsmul (k : ℕ) (c : Hand n) : size (k • c) = k • size c := by
  induction k with
  | zero => simp
  | succ k ih => simp [succ_nsmul, ih, Nat.add_mul]

def single (i : Fin (3 * n)) : Hand n :=
  fun j ↦ if j = i then 1 else 0

@[simp]
lemma single_apply (i : Fin (3 * n)) : single i i = 1 := by
  simp [single]

@[simp]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  simp [size, single]

abbrev pair (i : Fin (3 * n)) : Hand n :=
  2 • single i

abbrev triplet (i : Fin (3 * n)) : Hand n :=
  3 • single i

abbrev sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

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
  obtain ⟨tc, rc, hc⟩ := hc
  obtain ⟨td, rd, hd⟩ := hd
  use tc + td, rc + rd
  rw [hc, hd]
  simp only [Pi.add_apply, add_nsmul, Finset.sum_add_distrib]
  ac_rfl

def Winning (c : Hand n) : Prop :=
  Valid c ∧ ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + pair i

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  Winning (c + single i)

end Hand

end Mahjong
