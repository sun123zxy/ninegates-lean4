/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Wait.Basic
public import Ninegates.Meldable.Basic
public import Ninegates.Wait.Decidable.Basic
meta import Ninegates.Wait.Decidable.Basic

/-!
# Standard full waits

The eight parameter families and six order-one hands, with their full-wait and liveness
properties. This module also provides insertion of three consecutive ranks of multiplicity one.
General full waits have explicit meld placements; the six order-one hands and the exceptional
`E 2` are checked with `native_decide`, as permitted by this project's soundness policy.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

def insertSeqAt (c : Hand n) (k : Fin (3 * n)) : Hand (n + 1) :=
  ⟨fun i ↦ if h : i.val < k.val then c ⟨i.val, by omega⟩
           else if h : i.val < k.val + 3 then 1
           else c ⟨i.val - 3, by omega⟩⟩

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
  right_inv i := by
    apply Fin.ext
    by_cases hi₀ : i.val < k.val
    · simp [hi₀]
    · by_cases hi₁ : i.val < k.val + 3
      · simp [hi₀, hi₁]
        omega
      · have hi₂ : ¬i.val - 3 < k.val := by omega
        simp [hi₀, hi₁, hi₂]
        omega

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

namespace Standard

def A (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1⟩

@[grind =]
lemma A.apply (n : ℕ) (i : Fin (3 * n)) :
    A n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1 := by rfl

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

theorem A.isFullWait (n : ℕ) (hn : 0 < n) :
    IsFullWait (A n) := by
  have mod_three_cases (x : ℕ) : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  intro p
  constructor
  · rw [map_add, size_single, A.size]
    exact hn
  · rcases mod_three_cases p.val with hp | hp | hp
    on_goal 1 =>
      let q : Meldable.Placement n :=
        ⟨(fun _ ↦ 0), fun i ↦ if i.val + 2 < 3 * n ∧
          ((i.val % 3 = 1 ∧ i.val < p.val) ∨
            (i.val % 3 = 0 ∧ p.val ≤ i.val)) then 1 else 0, by
              constructor <;> intro i hi <;>
                simp only [ite_eq_right_iff] <;> intro h <;> grind⟩
      use q.toHand + triplet ⟨0, by omega⟩, ⟨3 * n - 1, by omega⟩,
        Meldable.add ⟨q, rfl⟩ Meldable.triplet
    on_goal 2 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 1 else 0),
          fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 1 ∧ i.val < p.val) ∨
              (i.val % 3 = 2 ∧ p.val < i.val)) then 1 else 0, by
              constructor <;> intro i hi <;>
                simp only [ite_eq_right_iff] <;> intro h <;> grind⟩
      use q.toHand, p, ⟨q, rfl⟩
    on_goal 3 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 * n - 1 then 1 else 0),
          fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 0 ∧ i.val < p.val) ∨
              (i.val % 3 = 2 ∧ p.val ≤ i.val)) then 1 else 0, by
              constructor <;> intro i hi <;>
                simp only [ite_eq_right_iff] <;> intro h <;> grind⟩
      use q.toHand, ⟨0, by omega⟩, ⟨q, rfl⟩
    all_goals
      ext i
      simp only [A.apply, add_apply, pair_apply, single_apply]
      by_cases hi₀ : i.val = 0; · grind
      by_cases hi₁ : i.val = 1; · simp_all; grind
      by_cases hi₂ : i.val = 3 * n - 1; · grind
      have hi₃ : 2 ≤ i.val := by omega
      have hi₄ : i.val ≤ 3 * n - 2 := by omega
      by_cases hi₅ : i.val = p.val; · grind
      rcases mod_three_cases i.val with himod | himod | himod
      all_goals simp_all; grind

theorem A.isLiveFullWait (n : ℕ) (hn : 0 < n) :
    IsLiveFullWait (A n) := by
  apply isLiveFullWait_iff_le_three.mpr
  refine ⟨A.isFullWait n hn, ?_⟩
  intro p
  simp only [A.apply]
  split_ifs <;> omega

lemma A.insertSeqAt (k : Fin (3 * n)) (hk : 0 < k.val) :
    (A n).insertSeqAt k = A (n + 1) := by
  ext i
  grind

def B (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 then 3 else if i.val = 3 * n - 4 then 4
    else if i.val = 3 * n - 1 then 0 else 1⟩

@[grind =]
lemma B.apply (n : ℕ) (i : Fin (3 * n)) :
    B n i = if i.val = 0 then 3 else if i.val = 3 * n - 4 then 4
    else if i.val = 3 * n - 1 then 0 else 1 := rfl

def B' (n : ℕ) : Hand n := reverse (B n)

@[simp]
lemma B'.eq_reverse (n : ℕ) : B' n = reverse (B n) := rfl

@[grind =]
lemma B'.apply (n : ℕ) (i : Fin (3 * n)) :
    B' n i = if i.val = 3 * n - 1 then 3 else if i.val = 3 then 4
      else if i.val = 0 then 0 else 1 := by
  simp only [B', reverse_apply, B.apply, Fin.rev]
  grind

def C (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 2 then 4 else if i.val = 3 * n - 2 then 3
    else if i.val = 3 * n - 1 then 0 else 1⟩

@[grind =]
lemma C.apply (n : ℕ) (i : Fin (3 * n)) :
    C n i = if i.val = 2 then 4 else if i.val = 3 * n - 2 then 3
    else if i.val = 3 * n - 1 then 0 else 1 := rfl

def C' (n : ℕ) : Hand n := reverse (C n)

@[simp]
lemma C'.eq_reverse (n : ℕ) : C' n = reverse (C n) := rfl

@[grind =]
lemma C'.apply (n : ℕ) (i : Fin (3 * n)) :
    C' n i = if i.val = 3 * n - 3 then 4 else if i.val = 1 then 3
      else if i.val = 0 then 0 else 1 := by
  simp only [C', reverse_apply, C.apply, Fin.rev]
  grind

def D (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else if i.val = 2 then 4
    else if i.val = 3 then 2 else if i.val = 3 * n - 2 then 3 else 1⟩

@[grind =]
lemma D.apply (n : ℕ) (i : Fin (3 * n)) :
    D n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else if i.val = 2 then 4
    else if i.val = 3 then 2 else if i.val = 3 * n - 2 then 3 else 1 := rfl

def D' (n : ℕ) : Hand n := reverse (D n)

@[simp]
lemma D'.eq_reverse (n : ℕ) : D' n = reverse (D n) := rfl

@[grind =]
lemma D'.apply (n : ℕ) (i : Fin (3 * n)) :
    D' n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 0
      else if i.val = 3 * n - 3 then 4 else if i.val = 3 * n - 4 then 2
      else if i.val = 1 then 3 else 1 := by
  simp only [D', reverse_apply, D.apply, Fin.rev]
  grind

def E (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 0
    else if (n = 2 ∧ (i.val = 2 ∨ i.val = 3)) ∨
      (n ≠ 2 ∧ (i.val = 3 ∨ i.val = 3 * n - 4)) then 4 else 1⟩

@[grind =]
lemma E.apply (n : ℕ) (i : Fin (3 * n)) :
    E n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 0
    else if (n = 2 ∧ (i.val = 2 ∨ i.val = 3)) ∨
      (n ≠ 2 ∧ (i.val = 3 ∨ i.val = 3 * n - 4)) then 4 else 1 := rfl

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

theorem B.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (B n) := by
  intro p
  constructor
  · rw [map_add, size_single, B.size n hn]
  · have hp : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by omega
    rcases hp with hp | hp | hp
    on_goal 1 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 0 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            (i.val = 3 * n - 4 ∨ (i.val < 3 * n - 4 ∧
            ((i.val % 3 = 1 ∧ i.val < p.val) ∨ (i.val % 3 = 0 ∧ p.val ≤ i.val)))) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨3 * n - 4, by omega⟩, ⟨q, rfl⟩
    on_goal 2 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 4 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 1 ∧ i.val < p.val) ∨ (i.val % 3 = 2 ∧ p.val < i.val)) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨p.val, by omega⟩, ⟨q, rfl⟩
    on_goal 3 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 * n - 4 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 0 ∧ i.val < p.val) ∨ (i.val % 3 = 2 ∧ p.val ≤ i.val)) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨0, by omega⟩, ⟨q, rfl⟩
    all_goals
      ext i
      simp only [B.apply, add_apply, pair_apply, single_apply,
        Meldable.Placement.toHand_apply]
      dsimp only [q]
      clear q
      by_cases hi₀ : i.val = 0; · grind (splits := 20)
      by_cases hi₁ : i.val = 1; · grind (splits := 20)
      by_cases hi₂ : i.val = 3 * n - 4; · grind (splits := 20)
      by_cases hi₃ : i.val = 3 * n - 3; · grind (splits := 20)
      by_cases hi₄ : i.val = 3 * n - 2; · grind (splits := 20)
      by_cases hi₅ : i.val = 3 * n - 1; · grind (splits := 20)
      by_cases hip : i.val = p.val; · grind (splits := 20)
      have hi : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hi with hi | hi | hi <;> grind (splits := 20)

theorem C.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (C n) := by
  intro p
  constructor
  · rw [map_add, size_single, C.size n hn]
  · have hp : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by omega
    rcases hp with hp | hp | hp
    on_goal 1 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 2 ∨ i.val = 3 * n - 2 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n - 1 ∧
            ((i.val % 3 = 0 ∧ i.val < p.val) ∨ (i.val % 3 = 1 ∧ p.val < i.val)) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨p.val, by omega⟩, ⟨q, rfl⟩
    on_goal 2 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 * n - 2 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n - 1 ∧
            (i.val = 0 ∨ (0 < i.val ∧
            ((i.val % 3 = 2 ∧ i.val < p.val) ∨ (i.val % 3 = 1 ∧ p.val ≤ i.val)))) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨2, by omega⟩, ⟨q, rfl⟩
    on_goal 3 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 2 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 0 ∧ i.val < p.val) ∨ (i.val % 3 = 2 ∧ p.val ≤ i.val)) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨3 * n - 2, by omega⟩, ⟨q, rfl⟩
    all_goals
      ext i
      simp only [C.apply, add_apply, pair_apply, single_apply,
        Meldable.Placement.toHand_apply]
      dsimp only [q]
      clear q
      by_cases hi0 : i.val = 0; · grind (splits := 20)
      by_cases hi1 : i.val = 1; · grind (splits := 20)
      by_cases hi2 : i.val = 2; · grind (splits := 20)
      by_cases hi3 : i.val = 3; · grind (splits := 20)
      by_cases hi4 : i.val = 3 * n - 4; · grind (splits := 20)
      by_cases hi5 : i.val = 3 * n - 3; · grind (splits := 20)
      by_cases hi6 : i.val = 3 * n - 2; · grind (splits := 20)
      by_cases hi7 : i.val = 3 * n - 1; · grind (splits := 20)
      by_cases hip : i.val = p.val; · grind (splits := 20)
      have hi : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hi with hi | hi | hi <;> grind (splits := 20)

theorem D.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (D n) := by
  intro p
  constructor
  · rw [map_add, size_single, D.size n hn]
  · by_cases hp₀ : p.val = 0
    on_goal 1 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 2 ∨ i.val = 3 * n - 2 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n - 1 ∧
            (i.val = 0 ∨ (4 ≤ i.val ∧ i.val % 3 = 1)) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨3, by omega⟩, ⟨q, rfl⟩
    on_goal 2 =>
      have hp : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by omega
      rcases hp with hp | hp | hp
      on_goal 1 =>
        let q : Meldable.Placement n :=
          ⟨(fun i ↦ if i.val = 2 ∨ i.val = 3 * n - 2 then 1 else 0),
            (fun i ↦ if i.val + 2 < 3 * n - 1 ∧
              (i.val = 1 ∨ (0 < i.val ∧
               ((i.val % 3 = 0 ∧ i.val < p.val) ∨
                 (i.val % 3 = 1 ∧ p.val < i.val)))) then 1 else 0), by
              constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
        use q.toHand, ⟨p.val, by omega⟩, ⟨q, rfl⟩
      on_goal 2 =>
        let q : Meldable.Placement n :=
          ⟨(fun i ↦ if i.val = 3 * n - 2 then 1 else 0),
            (fun i ↦ (if i.val = 1 then 1 else 0) +
              (if i.val + 2 < 3 * n - 1 ∧ 0 < i.val ∧
                ((i.val % 3 = 2 ∧ i.val < p.val) ∨
                  (i.val % 3 = 1 ∧ p.val ≤ i.val)) then 1 else 0)), by
              constructor <;> intro i hi <;> grind⟩
        use q.toHand, ⟨2, by omega⟩, ⟨q, rfl⟩
      on_goal 3 =>
        let q : Meldable.Placement n :=
          ⟨(fun i ↦ if i.val = 2 then 1 else 0),
            (fun i ↦ if i.val + 2 < 3 * n ∧
              (i.val = 1 ∨ (0 < i.val ∧
               ((i.val % 3 = 0 ∧ i.val < p.val) ∨
                 (i.val % 3 = 2 ∧ p.val ≤ i.val)))) then 1 else 0), by
              constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
        use q.toHand, ⟨3 * n - 2, by omega⟩, ⟨q, rfl⟩
    all_goals
      ext i
      simp only [D.apply, add_apply, pair_apply, single_apply,
        Meldable.Placement.toHand_apply]
      dsimp only [q]
      clear q
      by_cases hi0 : i.val = 0; · grind (splits := 20)
      by_cases hi1 : i.val = 1; · grind (splits := 20)
      by_cases hi2 : i.val = 2; · grind (splits := 20)
      by_cases hi3 : i.val = 3; · grind (splits := 20)
      by_cases hi4 : i.val = 3 * n - 4; · grind (splits := 20)
      by_cases hi5 : i.val = 3 * n - 3; · grind (splits := 20)
      by_cases hi6 : i.val = 3 * n - 2; · grind (splits := 20)
      by_cases hi7 : i.val = 3 * n - 1; · grind (splits := 20)
      by_cases hip : i.val = p.val; · grind (splits := 20)
      have hi : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hi with hi | hi | hi <;> grind (splits := 20)

theorem E.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (E n) := by
  by_cases hn₂ : n = 2
  · subst n; native_decide
  intro p
  constructor
  · rw [map_add, size_single, E.size n hn]
  · have hp : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by omega
    rcases hp with hp | hp | hp
    on_goal 1 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            (i.val = 3 * n - 4 ∨ (i.val < 3 * n - 4 ∧
            ((i.val % 3 = 1 ∧ i.val < p.val) ∨ (i.val % 3 = 0 ∧ p.val ≤ i.val)))) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨3 * n - 4, by omega⟩, ⟨q, rfl⟩
    on_goal 2 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 ∨ i.val = 3 * n - 4 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 1 ∧ i.val < p.val) ∨ (i.val % 3 = 2 ∧ p.val < i.val)) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨p.val, by omega⟩, ⟨q, rfl⟩
    on_goal 3 =>
      let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 * n - 4 then 1 else 0),
          (fun i ↦ if i.val + 2 < 3 * n ∧
            (i.val = 1 ∨ (0 < i.val ∧
            ((i.val % 3 = 0 ∧ i.val < p.val) ∨ (i.val % 3 = 2 ∧ p.val ≤ i.val)))) then 1 else 0), by
            constructor <;> intro i hi <;> simp only [ite_eq_right_iff] <;> grind⟩
      use q.toHand, ⟨3, by omega⟩, ⟨q, rfl⟩
    all_goals
      ext i
      simp only [E.apply, add_apply, pair_apply, single_apply,
        Meldable.Placement.toHand_apply]
      dsimp only [q]
      clear q
      by_cases hi0 : i.val = 0; · grind (splits := 20)
      by_cases hi1 : i.val = 1; · grind (splits := 20)
      by_cases hi2 : i.val = 2; · grind (splits := 20)
      by_cases hi3 : i.val = 3; · grind (splits := 20)
      by_cases hi4 : i.val = 3 * n - 4; · grind (splits := 20)
      by_cases hi5 : i.val = 3 * n - 3; · grind (splits := 20)
      by_cases hi6 : i.val = 3 * n - 2; · grind (splits := 20)
      by_cases hi7 : i.val = 3 * n - 1; · grind (splits := 20)
      by_cases hip : i.val = p.val; · grind (splits := 20)
      have hi : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hi with hi | hi | hi <;> grind (splits := 20)

theorem B'.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (B' n) := by
  simpa using (B.isFullWait n hn).reverse

theorem C'.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (C' n) := by
  simpa using (C.isFullWait n hn).reverse

theorem D'.isFullWait (n : ℕ) (hn : 2 ≤ n) : IsFullWait (D' n) := by
  simpa using (D.isFullWait n hn).reverse

theorem B.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (B n) := by
  intro hc
  have h := hc.le_three ⟨3 * n - 4, by omega⟩
  grind

theorem B'.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (B' n) := by
  intro hc
  have h := hc.le_three (⟨3 * n - 4, by omega⟩ : Fin (3 * n)).rev
  simp only [B'.eq_reverse, reverse_apply, Fin.rev_rev] at h
  grind

theorem C.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (C n) := by
  intro hc
  have h := hc.le_three ⟨2, by omega⟩
  grind

theorem C'.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (C' n) := by
  intro hc
  have h := hc.le_three (⟨2, by omega⟩ : Fin (3 * n)).rev
  simp only [C'.eq_reverse, reverse_apply, Fin.rev_rev] at h
  grind

theorem D.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (D n) := by
  intro hc
  have h := hc.le_three ⟨2, by omega⟩
  grind

theorem D'.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (D' n) := by
  intro hc
  have h := hc.le_three (⟨2, by omega⟩ : Fin (3 * n)).rev
  simp only [D'.eq_reverse, reverse_apply, Fin.rev_rev] at h
  grind

theorem E.not_isLiveFullWait (n : ℕ) (hn : 2 ≤ n) : ¬ IsLiveFullWait (E n) := by
  intro hc
  have h := hc.le_three ⟨if n = 2 then 2 else 3, by split_ifs <;> omega⟩
  grind

namespace One

def a : Hand 1 := ⟨![3, 1, 3]⟩

@[simp]
lemma a.apply (i : Fin 3) : a i = ![3, 1, 3] i := rfl

@[simp, grind =]
lemma a.size : Hand.size a = 7 := by decide

theorem a.isFullWait : IsFullWait a := by native_decide

theorem a.isLiveFullWait : IsLiveFullWait a := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨a.isFullWait, by decide⟩

def b : Hand 1 := ⟨![2, 3, 2]⟩

@[simp]
lemma b.apply (i : Fin 3) : b i = ![2, 3, 2] i := rfl

@[simp, grind =]
lemma b.size : Hand.size b = 7 := by decide

theorem b.isFullWait : IsFullWait b := by native_decide

theorem b.isLiveFullWait : IsLiveFullWait b := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨b.isFullWait, by decide⟩

def c : Hand 1 := ⟨![3, 3, 1]⟩

@[simp]
lemma c.apply (i : Fin 3) : c i = ![3, 3, 1] i := rfl

@[simp, grind =]
lemma c.size : Hand.size c = 7 := by decide

theorem c.isFullWait : IsFullWait c := by native_decide

theorem c.isLiveFullWait : IsLiveFullWait c := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨c.isFullWait, by decide⟩

def c' : Hand 1 := ⟨![1, 3, 3]⟩

@[simp]
lemma c'.apply (i : Fin 3) : c' i = ![1, 3, 3] i := rfl

@[simp, grind =]
lemma c'.size : Hand.size c' = 7 := by decide

theorem c'.isFullWait : IsFullWait c' := by native_decide

theorem c'.isLiveFullWait : IsLiveFullWait c' := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨c'.isFullWait, by decide⟩

def d : Hand 1 := ⟨![3, 2, 2]⟩

@[simp]
lemma d.apply (i : Fin 3) : d i = ![3, 2, 2] i := rfl

@[simp, grind =]
lemma d.size : Hand.size d = 7 := by decide

theorem d.isFullWait : IsFullWait d := by native_decide

theorem d.isLiveFullWait : IsLiveFullWait d := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨d.isFullWait, by decide⟩

def d' : Hand 1 := ⟨![2, 2, 3]⟩

@[simp]
lemma d'.apply (i : Fin 3) : d' i = ![2, 2, 3] i := rfl

@[simp, grind =]
lemma d'.size : Hand.size d' = 7 := by decide

theorem d'.isFullWait : IsFullWait d' := by native_decide

theorem d'.isLiveFullWait : IsLiveFullWait d' := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨d'.isFullWait, by decide⟩

end One

end Standard

end Mahjong.Hand
