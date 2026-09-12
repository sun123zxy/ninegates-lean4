/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Operations.Defs
public import Ninegates.Basic

/-!
## Basic properties of sequence insertion and removal
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

@[grind =]
lemma insertSeqAt_apply (c : Hand n) (k : Fin (3 * n))
    (i : Fin (3 * (n + 1))) : c.insertSeqAt k i =
    if _h : i.val < k.val then c ⟨i.val, by omega⟩
    else if _h : i.val < k.val + 3 then 1
    else c ⟨i.val - 3, by omega⟩ := rfl

@[simp]
lemma insertSeqAt_apply_of_lt (c : Hand n) (k : Fin (3 * n))
    (i : Fin (3 * (n + 1))) (hi : i.val < k.val) :
    c.insertSeqAt k i = c ⟨i.val, by omega⟩ := by grind

@[simp]
lemma insertSeqAt_apply_of_mem (c : Hand n) (k : Fin (3 * n))
    (i : Fin (3 * (n + 1))) (hi₀ : k.val ≤ i.val) (hi₁ : i.val < k.val + 3) :
    c.insertSeqAt k i = 1 := by grind

@[simp]
lemma insertSeqAt_apply_of_ge (c : Hand n) (k : Fin (3 * n))
    (i : Fin (3 * (n + 1))) (hi : k.val + 3 ≤ i.val) :
    c.insertSeqAt k i = c ⟨i.val - 3, by omega⟩ := by grind

@[grind =]
lemma removeSeqAt_apply (c : Hand (n + 1)) (k : Fin (3 * n))
    (i : Fin (3 * n)) :
    removeSeqAt c k i =
      if _h : i.val < k.val then c ⟨i.val, by omega⟩
      else c ⟨i.val + 3, by omega⟩ := rfl

@[simp]
lemma removeSeqAt_apply_of_lt (c : Hand (n + 1)) (k : Fin (3 * n))
    (i : Fin (3 * n)) (hi : i.val < k.val) :
    removeSeqAt c k i = c ⟨i.val, by omega⟩ := by grind

@[simp]
lemma removeSeqAt_apply_of_ge (c : Hand (n + 1)) (k : Fin (3 * n))
    (i : Fin (3 * n)) (hi : k.val ≤ i.val) :
    removeSeqAt c k i = c ⟨i.val + 3, by omega⟩ := by grind

@[simp, grind =]
lemma insertSeqAt_removeSeqAt (c : Hand (n + 1))
    (k : Fin (3 * n)) (h₀ : c ⟨k.val, by omega⟩ = 1)
    (h₁ : c ⟨k.val + 1, by omega⟩ = 1) (h₂ : c ⟨k.val + 2, by omega⟩ = 1) :
    (removeSeqAt c k).insertSeqAt k = c := by
  ext i; grind

@[grind →]
lemma HasSeqAt.exists_insertSeqAt {c : Hand (n + 1)}
    {k : Fin (3 * n)} (hc : HasSeqAt c k) (hk₀ : 0 < k.val) :
    ∃ d : Hand n, ∃ k : Fin (3 * n), 0 < k.val ∧ c = d.insertSeqAt k := by
  exact ⟨removeSeqAt c k, k, hk₀, by grind⟩

def insertSeqEquiv (k : Fin (3 * n)) :
    Fin (3 * n) ⊕ Fin 3 ≃ Fin (3 * (n + 1)) where
  toFun x := match x with
    | .inl i => ⟨if i.val < k.val then i.val else i.val + 3, by grind⟩
    | .inr j => ⟨k.val + j.val, by omega⟩
  invFun i :=
    if h₀ : i.val < k.val then .inl ⟨i.val, by omega⟩
    else if h₁ : i.val < k.val + 3 then .inr ⟨i.val - k.val, by omega⟩
    else .inl ⟨i.val - 3, by omega⟩
  left_inv x := by grind
  right_inv i := by grind

@[simp, grind =]
lemma insertSeqEquiv_inl_val (k : Fin (3 * n)) (i : Fin (3 * n)) :
    (insertSeqEquiv k (.inl i)).val = if i.val < k.val then i.val else i.val + 3 :=
  rfl

lemma insertSeqAt_add_single (c : Hand n) (k i : Fin (3 * n)) :
    (c + single i).insertSeqAt k =
      c.insertSeqAt k + single (insertSeqEquiv k (.inl i)) := by
  ext x
  grind

@[simp, grind =]
lemma insertSeqEquiv_inr_val (k : Fin (3 * n)) (i : Fin 3) :
    (insertSeqEquiv k (.inr i)).val = k.val + i.val := rfl

@[grind =]
lemma size_insertSeqAt (c : Hand n) (k : Fin (3 * n)) :
    size (c.insertSeqAt k) = size c + 3 := by
  have hinl (i : Fin (3 * n)) : c.insertSeqAt k (insertSeqEquiv k (.inl i)) = c i := by grind
  have hinr (i : Fin 3) : c.insertSeqAt k (insertSeqEquiv k (.inr i)) = 1 := by grind
  change (∑ i : Fin (3 * (n + 1)), c.insertSeqAt k i) =
    (∑ i : Fin (3 * n), c i) + 3
  calc
    _ = ∑ x : Fin (3 * n) ⊕ Fin 3, c.insertSeqAt k (insertSeqEquiv k x) :=
      (Equiv.sum_comp (insertSeqEquiv k) (fun i ↦ c.insertSeqAt k i)).symm
    _ = _ := by simp [Fintype.sum_sum_type, hinl, hinr]

end Mahjong.Hand
