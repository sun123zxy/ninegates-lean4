/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# Mahjong hands

## Main definitions

- A `Hand n` records the counting vector of a hand.
  It's a wrapper around `Fin (3 * n) → ℕ`.
  Recall that `![]` is Mathlib's convenient notation for functions over `Fin n`.

- `single`, `pair`, `triplet`, and `sequence` are the elementary tile patterns.

- `size` counts tiles, while `sum` is their value-weighted sum.

- `Valid c` requires every legal multiplicity of `c` to be at most four.

## Design notes

### Definition of `Hand`

We choose to define `Hand` as a wrapper around `Fin (3 * n) → ℕ`.
The main reason is that the counting vector representation
is mathematically idomatic and heavily used in our literature.
The drawback is that for algorithmic use,
some glue code is required to convert it into a `List`-like representation.

We come to this choice after trialing and erroring with many other representations:

- `Finsupp`: Allows flexible support and may be good at handling the edge cases,
  but it's current version in `Mathlib` is unfortunately uncomputable.

- `Multiset`: Each tile as an element, born computation-friendly.
  But as counting number of tiles is a fundamental operation in our development,
  Computable does not mean efficiently computable.

- `Vector` as the counting vector might be the best choice with both mathematical
  and computational friendliness. Many algorithms are already using it.
  However it's not a standard Mathlib accent.

Basic properties are in `Ninegates.Basic`.
-/

@[expose] public section

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

def sum : Hand n →+ ℕ where
  toFun c := ∑ i, i.val * c i
  map_zero' := by simp
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]

def single (i : Fin (3 * n)) : Hand n := ⟨fun j ↦ if j = i then 1 else 0⟩

def pair (i : Fin (3 * n)) : Hand n := 2 • single i

def triplet (i : Fin (3 * n)) : Hand n := 3 • single i

def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[grind =]
def Valid (c : Hand n) : Prop := ∀ i : Fin (3 * n), c i ≤ 4

instance (c : Hand n) : Decidable (Valid c) := by
  apply decidable_of_iff (∀ i, c i ≤ 4)
  simp [Valid]

/-- Reverse the order of the tile ranks. -/
def reverse : Hand n →+ Hand n where
  toFun c := ⟨fun i ↦ c i.rev⟩
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

end Hand

end Mahjong
