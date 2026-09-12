/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Standard.Insert

/-!
# Basic properties of standard families

Hand sizes for the eight families and coordinate formulas and sizes for the six order-one hands.
Full-wait and liveness results are in `Ninegates.Standard.Wait`.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

namespace Standard

@[simp, grind =]
lemma A.size (n : ℕ) (hn : 0 < n) :
    size (A n) = 3 * n + 4 := by
  simp only [size_eq_sum, A.apply]
  have hsplit (i : Fin (3 * n)) :
      (if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1) =
        1 + (if i.val = 0 then 2 else 0) +
          (if i.val = 3 * n - 1 then 2 else 0) := by grind
  have hsingle (k : ℕ) (hk : k < 3 * n) :
      (∑ i : Fin (3 * n), if i.val = k then 2 else 0) = 2 := by
    rw [Finset.sum_eq_single ⟨k, hk⟩] <;> grind
  simp [hsplit, Finset.sum_add_distrib, hsingle 0 (by omega), hsingle (3 * n - 1) (by omega)]

@[simp, grind =]
lemma B.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (B n) = 3 * n + 4 := by
  have h : B n + triplet ⟨3 * n - 1, by omega⟩ =
      A n + triplet ⟨3 * n - 4, by omega⟩ := by
    ext i
    simp only [B.apply, A.apply, add_apply, triplet_apply]
    grind
  have hs := congrArg Hand.size h
  simp only [map_add, size_triplet, A.size n (by omega)] at hs
  omega

@[simp, grind =]
lemma B'.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (B' n) = 3 * n + 4 := by
  simpa using B.size n hn

@[simp, grind =]
lemma C.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (C n) = 3 * n + 4 := by
  have h : C n + pair ⟨0, by omega⟩ + triplet ⟨3 * n - 1, by omega⟩ =
      A n + triplet ⟨2, by omega⟩ + pair ⟨3 * n - 2, by omega⟩ := by
    ext i
    simp only [C.apply, A.apply, add_apply, triplet_apply, pair_apply]
    grind
  have hs := congrArg Hand.size h
  simp only [map_add, size_triplet, size_pair, A.size n (by omega)] at hs
  omega

@[simp, grind =]
lemma C'.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (C' n) = 3 * n + 4 := by
  simpa using C.size n hn

@[simp, grind =]
lemma D.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (D n) = 3 * n + 4 := by
  have h : D n + triplet ⟨0, by omega⟩ + triplet ⟨3 * n - 1, by omega⟩ =
      A n + triplet ⟨2, by omega⟩ + single ⟨3, by omega⟩ + pair ⟨3 * n - 2, by omega⟩ := by
    ext i
    simp only [D.apply, A.apply, add_apply, triplet_apply, pair_apply, single_apply]
    grind
  have hs := congrArg Hand.size h
  simp only [map_add, size_triplet, size_pair, size_single, A.size n (by omega)] at hs
  omega

@[simp, grind =]
lemma D'.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (D' n) = 3 * n + 4 := by
  simpa using D.size n hn

@[simp, grind =]
lemma E.size (n : ℕ) (hn : 2 ≤ n) : Hand.size (E n) = 3 * n + 4 := by
  by_cases hn₂ : n = 2
  · subst n; decide
  have h : E n + triplet ⟨0, by omega⟩ + triplet ⟨3 * n - 1, by omega⟩ =
      A n + triplet ⟨3, by omega⟩ + triplet ⟨3 * n - 4, by omega⟩ := by
    ext i
    simp only [E.apply, A.apply, add_apply, triplet_apply]
    grind
  have hs := congrArg Hand.size h
  simp only [map_add, size_triplet, A.size n (by omega)] at hs
  omega

namespace One

@[simp]
lemma a.apply (i : Fin 3) : a i = ![3, 1, 3] i := rfl

@[simp, grind =]
lemma a.size : Hand.size a = 7 := by decide

@[simp]
lemma b.apply (i : Fin 3) : b i = ![2, 3, 2] i := rfl

@[simp, grind =]
lemma b.size : Hand.size b = 7 := by decide

@[simp]
lemma c.apply (i : Fin 3) : c i = ![3, 3, 1] i := rfl

@[simp, grind =]
lemma c.size : Hand.size c = 7 := by decide

@[simp]
lemma c'.apply (i : Fin 3) : c' i = ![1, 3, 3] i := rfl

@[simp, grind =]
lemma c'.size : Hand.size c' = 7 := by decide

@[simp]
lemma d.apply (i : Fin 3) : d i = ![3, 2, 2] i := rfl

@[simp, grind =]
lemma d.size : Hand.size d = 7 := by decide

@[simp]
lemma d'.apply (i : Fin 3) : d' i = ![2, 2, 3] i := rfl

@[simp, grind =]
lemma d'.size : Hand.size d' = 7 := by decide

end One

end Standard

end Mahjong.Hand
