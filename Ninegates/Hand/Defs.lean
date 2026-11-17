/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

/-!
# Virtual hands for the new paper

A virtual hand is an integer multiplicity vector on `3 * n` ranks. Actual hands
are specified by `Nonnegative`, rather than a separate representation, so that
subtraction is always integer subtraction. The order and meld count are
independent; no size condition is built into the representation.

Indices are zero-based in Lean. `rank i = i.val + 1` is the one-based paper rank;
both `rankSum` and `classSize` use that convention.
-/

@[expose] public section

namespace Mahjong

abbrev Rank (n : ℕ) := Fin (3 * n)
abbrev VirtualHand (n : ℕ) := Rank n → ℤ

namespace VirtualHand

variable {n : ℕ}

def rank (i : Rank n) : ℤ := i.val + 1
def rankClass (i : Rank n) : ZMod 3 := rank i

/-- The virtual vector represents an actual hand. -/
def Nonnegative (c : VirtualHand n) : Prop := 0 ≤ c

/-- Multiplicities lie between zero and an independently chosen copy bound. -/
def Bounded (cap : ℕ) (c : VirtualHand n) : Prop :=
  Nonnegative c ∧ ∀ i, c i ≤ cap

def Valid (c : VirtualHand n) : Prop := Bounded 4 c

def single (i : Rank n) : VirtualHand n := fun j ↦ if j = i then 1 else 0
def pair (i : Rank n) : VirtualHand n := (2 : ℤ) • single i
def triplet (i : Rank n) : VirtualHand n := (3 : ℤ) • single i
def sequence (i : Fin (3 * n - 2)) : VirtualHand n :=
  single ⟨i.val, by omega⟩ + single ⟨i.val + 1, by omega⟩ + single ⟨i.val + 2, by omega⟩

def size : VirtualHand n →ₗ[ℤ] ℤ where
  toFun c := ∑ i, c i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

def rankSum : VirtualHand n →ₗ[ℤ] ℤ where
  toFun c := ∑ i, rank i * c i
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum, mul_left_comm]

def classSize (r : ZMod 3) : VirtualHand n →ₗ[ℤ] ℤ where
  toFun c := ∑ i ∈ Finset.univ.filter (fun i : Rank n ↦ rankClass i = r), c i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

def reverse : VirtualHand n →ₗ[ℤ] VirtualHand n where
  toFun c := fun i ↦ c i.rev
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end VirtualHand
end Mahjong
