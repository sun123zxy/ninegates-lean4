/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Defs

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

/-! ## Sequence insertion and removal -/

def insertSeqAt (c : Hand n) (k : Fin (3 * n)) : Hand (n + 1) :=
  ⟨fun i ↦ if h : i.val < k.val then c ⟨i.val, by omega⟩
           else if h : i.val < k.val + 3 then 1
           else c ⟨i.val - 3, by omega⟩⟩

/-- A hand has a sequence of three singleton tiles at `k`. -/
abbrev HasSeqAt (c : Hand (n + 1)) (k : Fin (3 * n)) : Prop :=
  c ⟨k.val, by omega⟩ = 1 ∧ c ⟨k.val + 1, by omega⟩ = 1 ∧
    c ⟨k.val + 2, by omega⟩ = 1

/-- Remove the three positions starting at `k`, shifting the suffix left. -/
def removeSeqAt (c : Hand (n + 1)) (k : Fin (3 * n)) : Hand n :=
  ⟨fun i ↦
    if _h : i.val < k.val then c ⟨i.val, by omega⟩
    else c ⟨i.val + 3, by omega⟩⟩

end Mahjong.Hand
