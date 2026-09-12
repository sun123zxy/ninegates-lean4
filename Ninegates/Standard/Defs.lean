/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Defs

/-!
# Standard full-wait families

The eight parameter families, six order-one hands, and their membership predicates.
Full-wait and liveness properties are in `Ninegates.Standard.Wait`.
Coordinate formulas and insertion properties are in `Ninegates.Standard.Insert`.
-/

@[expose] public section

namespace Mahjong.Hand

namespace Standard

def A (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1⟩

def B (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 then 3 else if i.val = 3 * n - 4 then 4
    else if i.val = 3 * n - 1 then 0 else 1⟩

def B' (n : ℕ) : Hand n := reverse (B n)

def C (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 2 then 4 else if i.val = 3 * n - 2 then 3
    else if i.val = 3 * n - 1 then 0 else 1⟩

def C' (n : ℕ) : Hand n := reverse (C n)

def D (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else if i.val = 2 then 4
    else if i.val = 3 then 2 else if i.val = 3 * n - 2 then 3 else 1⟩

def D' (n : ℕ) : Hand n := reverse (D n)

def E (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 0
    else if (n = 2 ∧ (i.val = 2 ∨ i.val = 3)) ∨
      (n ≠ 2 ∧ (i.val = 3 ∨ i.val = 3 * n - 4)) then 4 else 1⟩

namespace One

def a : Hand 1 := ⟨![3, 1, 3]⟩

def b : Hand 1 := ⟨![2, 3, 2]⟩

def c : Hand 1 := ⟨![3, 3, 1]⟩

def c' : Hand 1 := ⟨![1, 3, 3]⟩

def d : Hand 1 := ⟨![3, 2, 2]⟩

def d' : Hand 1 := ⟨![2, 2, 3]⟩

end One

end Standard

/-- Equality to one of the eight standard families for orders at least two. -/
abbrev IsEightFamily {n : ℕ} (c : Hand n) : Prop :=
  c = Standard.A n ∨
  c = Standard.B n ∨
  c = Standard.B' n ∨
  c = Standard.C n ∨
  c = Standard.C' n ∨
  c = Standard.D n ∨
  c = Standard.D' n ∨
  c = Standard.E n

/-- Equality to one of the six standard order-one hands. -/
abbrev IsOrderOneFamily (c : Hand 1) : Prop :=
  c = Standard.One.a ∨
  c = Standard.One.b ∨
  c = Standard.One.c ∨
  c = Standard.One.c' ∨
  c = Standard.One.d ∨
  c = Standard.One.d'

end Mahjong.Hand
