/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Basic
public import Ninegates.Hand.OrderOne
public import Ninegates.Meldable.OrderOne
public import Ninegates.Meldable.Virtual
public import Ninegates.Standard.One
public import Ninegates.Wait.OrderOne

/-! Every order-one full wait contains one of the six smallest full waits,
with a meldable difference. Hence these are exactly the minimal ones. -/

@[expose] public section

namespace Mahjong.VirtualHand

namespace OrderOne

private def base (i : Rank 1) (high : Bool) : VirtualHand 1 := fun j ↦
  if j = i then (if high then 3 else 1) else (if high then 2 else 3)

private lemma base_family (i : Rank 1) (high : Bool) : Standard.OrderOneFamily (base i high) := by
  fin_cases i <;> cases high
  · refine ⟨3, ?_⟩
    ext j
    fin_cases j <;> norm_num [base, Standard.One]
  · refine ⟨4, ?_⟩
    ext j
    fin_cases j <;> norm_num [base, Standard.One]
  · refine ⟨0, ?_⟩
    ext j
    fin_cases j <;> norm_num [base, Standard.One]
  · refine ⟨1, ?_⟩
    ext j
    fin_cases j <;> norm_num [base, Standard.One]
  · refine ⟨2, ?_⟩
    ext j
    fin_cases j <;> norm_num [base, Standard.One]
  · refine ⟨5, ?_⟩
    ext j
    fin_cases j <;> norm_num [base, Standard.One]

private lemma base_class (i : Rank 1) (high : Bool) : fixedClass (base i high) = rankClass i := by
  fin_cases i <;> cases high <;> decide +kernel

lemma exists_standard_le {m : ℕ} {c : VirtualHand 1} (full : IsFullWait m c) :
    ∃ k : Fin 6, Standard.One k ≤ c ∧ fixedClass (Standard.One k) = fixedClass c := by
  obtain ⟨i, fixed_i⟩ := exists_rankClass (n := 1) (by decide) (fixedClass c)
  have threshold := ((full_iff c).mp full).2
  have fixed_lower : 1 ≤ c i := by
    simpa only [pairThreshold, fixed_i, ite_true] using threshold i
  have count := full.size_cast
  have other {j : Rank 1} (different : j ≠ i) : 2 ≤ c j ∧ ((c j : ZMod 3) + 1 = c i) := by
    have nonfixed : rankClass j ≠ fixedClass c := by
      intro same
      exact different (rankClass_orderOne_injective (same.trans fixed_i.symm))
    have lower : 2 ≤ c j := by
      simpa only [pairThreshold, ite_eq_right nonfixed] using threshold j
    have residue := classSize_nonfixed_congruence count (rankClass j) nonfixed
    rw [classSize_orderOne, ← fixed_i, classSize_orderOne] at residue
    exact ⟨lower, residue⟩
  let high : Bool := decide (c i % 3 = 0)
  have dominated : base i high ≤ c := by
    intro j
    by_cases same : j = i
    · subst j
      simp only [base, ite_true]
      by_cases residue : c i % 3 = 0
      · simp only [high, residue, decide_true, ite_true]
        omega
      · simpa only [high, residue, decide_false, Bool.false_eq_true, ite_false] using fixed_lower
    · obtain ⟨lower, congruent⟩ := other same
      simp only [base, ite_eq_right same]
      by_cases residue : c i % 3 = 0
      · simpa only [high, residue, decide_true, ite_true] using lower
      · simp only [high, residue, decide_false, Bool.false_eq_true, ite_false]
        have not_two : c j ≠ 2 := by
          intro two
          rw [two] at congruent
          have zero : (c i : ZMod 3) = 0 := by
            calc
              _ = (2 : ZMod 3) + 1 := congruent.symm
              _ = 0 := by decide +kernel
          have divided := (ZMod.intCast_eq_intCast_iff' (c i) 0 3).mp zero
          norm_num only [Nat.cast_ofNat, Int.zero_emod] at divided
          exact residue divided
        omega
  obtain ⟨k, equal⟩ := base_family i high
  refine ⟨k, ?_, ?_⟩
  · simpa only [← equal] using dominated
  · rw [← equal, base_class, fixed_i]

end OrderOne

lemma IsFullWait.exists_orderOne_decomposition {m : ℕ} {c : VirtualHand 1}
    (full : IsFullWait m c) : ∃ k : Fin 6, Meldable (c - Standard.One k) := by
  obtain ⟨k, dominated, same_class⟩ := OrderOne.exists_standard_le full
  refine ⟨k, ?_⟩
  apply VirtuallyMeldable.meldable_orderOne _ (sub_nonneg.mpr dominated)
  apply (virtuallyMeldable_iff_size_rankSum _).mpr
  constructor
  · rw [map_sub, full.2.1, (Standard.One_live k).1.2.1]
    push_cast
    simp only [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
    decide +kernel
  · rw [map_sub]
    push_cast
    change fixedClass c - fixedClass (Standard.One k) = 0
    rw [same_class, sub_self]

lemma orderOne_isMinimalFullWait_iff {m : ℕ} {c : VirtualHand 1} :
    IsMinimalFullWait m c ↔ m = 2 ∧ Standard.OrderOneFamily c := by
  constructor
  · intro minimal
    obtain ⟨k, difference⟩ := minimal.full.exists_orderOne_decomposition
    have empty := minimal.minimal (Standard.One_live k).1 difference
      (show c = Standard.One k + (c - Standard.One k) by abel)
    have equal : c = Standard.One k := sub_eq_zero.mp empty
    have count := minimal.full.2.1
    rw [equal, (Standard.One_live k).1.2.1] at count
    exact ⟨by omega, k, equal⟩
  · rintro ⟨rfl, k, rfl⟩
    exact (Standard.One_live k).1.minimal_succ

end Mahjong.VirtualHand
