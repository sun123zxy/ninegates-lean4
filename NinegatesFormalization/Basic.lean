import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FunLike.IsApply
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Mahjong hands

## Main definitions

- A `Hand n` records the counting vector of a hand.
  It's a wrapper around `Fin (3 * n) → ℕ`.
- `single`, `pair`, `triplet`, and `sequence` are the elementary tile patterns.
- `size` counts tiles, while `sum` is their value-weighted sum.
- `Valid c` requires every legal multiplicity of `c` to be at most four.

## Design notes

### Definition of `Hand`

TODO: Alternative choices of defintion of `Hand`.

### Comparison convention of `Fin`

When comparing `i j : Fin (3 * n)`, we tend to retreat to `Nat` by `Fin.val`.
That is, write `i.val < j.val` instead of `i < j`, or `i.val = j.val` instead of `i = j`.
This helps us to maintain a canonical writing and a smooth proof automation,
as comparison on `Fin` is defined in terms of the underlying `Nat` comparison anyway.

### Hide of `∑`

As a general policy in this library, if a definition mentions `∑`,
we shall hide it from the downstream, as `∑` often breaks proof automation.

Thus we refrain from annotate `Hand`'s defining lemma with `@[grind]` or `@[simp]`.
We provide `grind`/`simp`-annotated lemmas free of `∑` for downstream use,
and non-`grind`/`simp`-annotated `xxx_eq_sum` lemmas for the rare occasions when `∑` is needed.
-/

namespace Mahjong

structure Hand (n : ℕ) where
  count : Fin (3 * n) → ℕ
deriving DecidableEq

namespace Hand

variable {n : ℕ}

instance : FunLike (Hand n) (Fin (3 * n)) ℕ where
  coe c := c.count
  coe_injective _ _ h := by
    cases ‹Hand n›
    cases ‹Hand n›
    congr

@[simp, grind =]
lemma mk_apply (count : Fin (3 * n) → ℕ) (i : Fin (3 * n)) :
    (⟨count⟩ : Hand n) i = count i := rfl

@[ext, grind ext]
lemma ext {c d : Hand n} (h : ∀ i, c i = d i) : c = d := DFunLike.ext c d h

instance : Zero (Hand n) := ⟨⟨0⟩⟩

instance : Add (Hand n) :=
  ⟨fun c d ↦ ⟨c.count + d.count⟩⟩

instance : SMul ℕ (Hand n) :=
  ⟨fun k c ↦ ⟨k • c.count⟩⟩

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
  add_assoc c d e := by apply DFunLike.ext; simp [add_assoc]
  zero_add c := by apply DFunLike.ext; simp
  add_zero c := by apply DFunLike.ext; simp
  add_comm c d := by apply DFunLike.ext; simp [add_comm]
  nsmul_zero k := by apply DFunLike.ext; simp
  nsmul_succ k c := by apply DFunLike.ext; simp [Nat.succ_mul, add_comm]

def size : Hand n →+ ℕ where
  toFun c := ∑ i, c i
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

lemma size_eq_sum (c : Hand n) : size c = ∑ i, c i := rfl

def sum : Hand n →+ ℕ where
  toFun c := ∑ i, i.val * c i
  map_zero' := by simp
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]

lemma sum_eq_sum (c : Hand n) : sum c = ∑ i, i.val * c i := rfl

def single (i : Fin (3 * n)) : Hand n := ⟨fun j ↦ if j = i then 1 else 0⟩

@[simp, grind =]
lemma single_apply (i j : Fin (3 * n)) :
    single i j = if j.val = i.val then 1 else 0 := by
  grind [single]

@[simp, grind =]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  simp [size, single]

@[simp, grind =]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by
  simp [sum, single]

def pair (i : Fin (3 * n)) : Hand n := 2 • single i

@[simp, grind =]
lemma pair_apply (i j : Fin (3 * n)) :
    pair i j = if j.val = i.val then 2 else 0 := by simp [pair]

@[simp, grind =]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by simp [pair]

@[simp, grind =]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by simp [pair]

def triplet (i : Fin (3 * n)) : Hand n := 3 • single i

@[simp, grind =]
lemma triplet_apply (i j : Fin (3 * n)) :
    triplet i j = if j.val = i.val then 3 else 0 := by grind [triplet]

@[simp, grind =]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by simp [triplet]

@[simp, grind =]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by simp [triplet]

def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[simp, grind =]
lemma sequence_apply (i : Fin (3 * n - 2)) (j : Fin (3 * n)) :
    sequence i j = if j.val = i.val ∨ j.val = i.val + 1 ∨ j.val = i.val + 2 then 1 else 0 := by
  grind [sequence]

@[simp, grind =]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by
  grind [sequence]

@[simp, grind =]
lemma sum_sequence (i : Fin (3 * n - 2)) : sum (sequence i) = 3 * (i.val + 1) := by
  grind [sequence]

@[grind =]
def Valid (c : Hand n) : Prop := ∀ i : Fin (3 * n), c i ≤ 4

end Hand

end Mahjong
