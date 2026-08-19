import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Mahjong hands

## Representation

A `Hand n` records the multiplicities of `3 * n` consecutive tile values.  Its
private representation is a function on `Fin (3 * n)`.  Its public `FunLike`
interface extends that function by zero to integer coordinates, so expressions such
as `c (i - 1)` remain meaningful at the boundary without carrying `Fin` proofs.

## Main definitions

* `Hand.ofFn` constructs a hand from its finite representation.
* `single`, `pair`, `triplet`, and `sequence` are the elementary tile patterns.
* `size` counts tiles, while `sum` is their value-weighted sum.
* `Valid c` requires every legal multiplicity of `c` to be at most four.

Hands form an additive commutative monoid, and `size` and `sum` are additive
homomorphisms.  Meld decompositions and winning hands are deliberately absent from
this foundational module.
-/

namespace Mahjong

namespace Internal

@[grind =]
def extend {m : ℕ} (f : Fin m → ℕ) (i : ℤ) : ℕ :=
  if h : 0 ≤ i ∧ i < m then f ⟨i.toNat, by omega⟩ else 0

@[simp, grind =]
lemma extend_coe {m : ℕ} (f : Fin m → ℕ) (i : Fin m) :
    extend f i.val = f i := by
  grind [extend]

@[simp, grind =]
lemma extend_of_lt_zero {m : ℕ} (f : Fin m → ℕ) (i : ℤ) (hi : i < 0) :
    extend f i = 0 := by simp [extend, hi]

@[simp, grind =]
lemma extend_of_ge {m : ℕ} (f : Fin m → ℕ) (i : ℤ) (hi : m ≤ i) :
    extend f i = 0 := by simp [extend, show ¬(0 ≤ i ∧ i < m) by omega]

@[simp, grind =]
lemma extend_zero {m : ℕ} (i : ℤ) :
    extend (0 : Fin m → ℕ) i = 0 := by simp [extend]

@[grind =]
lemma extend_add {m : ℕ} (f g : Fin m → ℕ) (i : ℤ) :
    extend (f + g) i = extend f i + extend g i := by
  by_cases h : 0 ≤ i ∧ i < m <;> simp [extend, h]

@[simp, grind =]
lemma extend_nsmul {m : ℕ} (k : ℕ) (f : Fin m → ℕ) (i : ℤ) :
    extend (k • f) i = k * extend f i := by
  by_cases h : 0 ≤ i ∧ i < m <;> simp [extend, h]

@[simp]
lemma extend_single {m : ℕ} (a : ℕ) (i : Fin m) (j : ℤ) :
    extend (fun k ↦ if k = i then a else 0) j =
      if j = i.val then a else 0 := by
  grind [extend]

@[simp]
lemma sum_ite_eq_extend {m : ℕ} (a : ℕ) (f : Fin m → ℕ) (i : ℤ) (d : ℕ) :
    (∑ j, if i = j.val + d then a * f j else 0) = a * extend f (i - d) := by
  simp only [extend]
  split
  next h =>
    let j : Fin m := ⟨(i - d).toNat, by omega⟩
    have hj : (j.val : ℤ) = i - d := Int.toNat_of_nonneg h.1
    have heq (k : Fin m) : (i = k.val + d) ↔ k = j := by grind
    simp only [heq]
    simp [j]
  next h =>
    have hout (j : Fin m) : i ≠ j.val + d := by omega
    simp [hout]

end Internal

open Internal

structure Hand (n : ℕ) where
  private mk ::
  private count : Fin (3 * n) → ℕ

namespace Hand

variable {n : ℕ}

def ofFn (f : Fin (3 * n) → ℕ) : Hand n := .mk f

instance : FunLike (Hand n) ℤ ℕ where
  coe c := extend c.count
  coe_injective := by
    intro c d h
    cases c
    cases d
    congr
    funext i
    simpa using congrFun h i.val

@[grind =]
lemma ofFn_apply (f : Fin (3 * n) → ℕ) (i : ℤ) :
    ofFn f i =
      if h : 0 ≤ i ∧ i < 3 * n then f ⟨i.toNat, by omega⟩ else 0 := by
  rfl

@[simp 1100, grind =]
lemma ofFn_apply_fin (f : Fin (3 * n) → ℕ) (i : Fin (3 * n)) :
    ofFn f i.val = f i :=
  extend_coe _ _

@[simp, grind =]
lemma apply_of_lt_zero (c : Hand n) (i : ℤ) (hi : i < 0) : c i = 0 :=
  extend_of_lt_zero _ _ hi

@[simp, grind =]
lemma apply_of_ge (c : Hand n) (i : ℤ) (hi : 3 * n ≤ i) : c i = 0 :=
  extend_of_ge _ _ hi

lemma ext_fin {c d : Hand n}
    (h : ∀ i : Fin (3 * n), c i = d i) : c = d := by
  cases c; cases d; congr; funext i
  have hi := h ⟨i, by omega⟩
  change extend _ i = extend _ i at hi
  simpa using hi

@[ext]
lemma ext {c d : Hand n}
    (h : ∀ i : ℤ, 0 ≤ i → i < 3 * n → c i = d i) : c = d := by
  cases c; cases d; congr; funext i
  have hi := h i.val (by omega) (by omega)
  change extend _ i.val = extend _ i.val at hi
  simpa using hi

instance : Zero (Hand n) := ⟨ofFn 0⟩

instance : Add (Hand n) :=
  ⟨fun c d ↦ ofFn (c.count + d.count)⟩

instance : SMul ℕ (Hand n) :=
  ⟨fun k c ↦ ofFn (k • c.count)⟩

instance : IsZeroApply (Hand n) ℤ ℕ where
  zero_apply _ := extend_zero _

instance : IsAddApply (Hand n) ℤ ℕ where
  add_apply _ _ _ := extend_add _ _ _

instance : IsSMulApply ℕ (Hand n) ℤ ℕ where
  smul_apply _ _ _ := extend_nsmul _ _ _

instance : AddCommMonoid (Hand n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc c d e := by ext i; simp [add_assoc]
  zero_add c := by ext i; simp
  add_zero c := by ext i; simp
  add_comm c d := by ext i; simp [add_comm]
  nsmul_zero k := by ext i; simp
  nsmul_succ k c := by ext i; simp [Nat.succ_mul, add_comm]

def size : Hand n →+ ℕ where
  toFun c := ∑ i : Fin (3 * n), c i
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

def sum : Hand n →+ ℕ where
  toFun c := ∑ i : Fin (3 * n), i.val * c i.val
  map_zero' := by simp
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]

@[grind =]
def single (i : Fin (3 * n)) : Hand n := ofFn fun j ↦ if j = i then 1 else 0

@[grind =]
lemma single_apply (i : Fin (3 * n)) (j : ℤ) :
    single i j = if j = i.val then 1 else 0 :=
  extend_single 1 i j

@[grind =]
lemma single_apply_fin (i j : Fin (3 * n)) :
    single i j = if j = i then 1 else 0 := by
  grind

@[simp, grind =]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  simp [size, single]

@[simp, grind =]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by
  simp [sum, single]

@[grind =]
def pair (i : Fin (3 * n)) : Hand n := 2 • single i

@[grind =]
lemma pair_apply (i : Fin (3 * n)) (j : ℤ) :
    pair i j = if j = i.val then 2 else 0 := by grind [pair]

@[grind =]
lemma pair_apply_fin (i j : Fin (3 * n)) :
    pair i j = if j = i then 2 else 0 := by grind [pair]

@[grind =]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by simp [pair]

@[simp, grind =]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by simp [pair]

@[grind =]
def triplet (i : Fin (3 * n)) : Hand n := 3 • single i

@[grind =]
lemma triplet_apply (i : Fin (3 * n)) (j : ℤ) :
    triplet i j = if j = i.val then 3 else 0 := by grind [triplet]

@[grind =]
lemma triplet_apply_fin (i j : Fin (3 * n)) :
    triplet i j = if j = i then 3 else 0 := by grind [triplet]

@[simp, grind =]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by simp [triplet]

@[simp, grind =]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by simp [triplet]

@[grind =]
def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[grind =]
lemma sequence_apply (i : Fin (3 * n - 2)) (j : ℤ) :
    sequence i j =
      if j = i.val ∨ j = i.val + 1 ∨ j = i.val + 2 then 1 else 0 := by
  simp only [sequence, add_apply, single_apply]
  split_ifs <;> omega

@[simp, grind =]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by simp [sequence]

@[simp, grind =]
lemma sum_sequence (i : Fin (3 * n - 2)) :
    sum (sequence i) = 3 * (i.val + 1) := by
  simp [sequence]
  omega

def Valid (c : Hand n) : Prop := ∀ i : Fin (3 * n), c i.val ≤ 4

end Hand

end Mahjong
