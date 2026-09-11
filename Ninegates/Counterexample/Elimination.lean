/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Counterexample.EnumSpec
public import Ninegates.Wait.Decidable.Basic
meta import Ninegates.Counterexample.EnumAlgo
meta import Ninegates.Wait.Decidable.Basic

/-!
# Elimination of the finite counterexample candidates

This file contains computational certificates for the finite candidates.
It uses the enumeration algorithm established in `EnumSpec` combined with
plain decidable checks of the relevant counterexample predicates.

The `native_decide` is used. The `meta import`s make the enumeration and decision
procedures available for compile-time execution of the certificate.
-/

@[expose] public section

namespace Mahjong.Hand.Counterexample

theorem candidates_no_CE (n : Nat) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    ∀ c ∈ Candidates n, ¬ IsCE c := by
  have hcertificate :
      (Candidates n).all (fun c => decide (¬ IsCE c)) = true := by
    interval_cases n <;> native_decide
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp hcertificate c hc)

theorem orderOne_candidates_classified :
    ∀ c ∈ Candidates 1, IsFullWait c → IsOrderOneFamily c := by
  have hcertificate :
      (Candidates 1).all
        (fun c => decide (IsFullWait c → IsOrderOneFamily c)) = true := by
    native_decide
  intro c hc hfull
  exact (of_decide_eq_true (List.all_eq_true.mp hcertificate c hc)) hfull

theorem fullWait_classification (n : Nat) (hn : 2 ≤ n) (c : Hand n)
    (hc : IsFullWait c) : IsEightFamily c := by
  classical
  by_contra hfamily
  let hex : ∃ m, 2 ≤ m ∧ ∃ d : Hand m, IsCE d :=
    ⟨n, hn, c, ⟨hc, hfamily⟩⟩
  let m := Nat.find hex
  obtain ⟨hm, d, hd⟩ := Nat.find_spec hex
  have hmin : ∀ k, 2 ≤ k → k < m → ¬ HasCE k := by
    intro k hk hkm hcounterexample
    have hspec := Nat.find_min' hex ⟨hk, hcounterexample⟩
    omega
  have hdmem := mem_candidates_of_minimal hm hd hmin
  have hm' : m ≤ 7 := (mem_candidates_iff.mp hdmem).2.1
  exact candidates_no_CE m hm hm' d hdmem hd

theorem isFullWait_iff_eightFamily (n : Nat) (hn : 2 ≤ n) (c : Hand n) :
    IsFullWait c ↔ IsEightFamily c := by
  constructor
  · exact fullWait_classification n hn c
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Standard.A.isFullWait n (by omega)
    · exact Standard.B.isFullWait n hn
    · exact Standard.B'.isFullWait n hn
    · exact Standard.C.isFullWait n hn
    · exact Standard.C'.isFullWait n hn
    · exact Standard.D.isFullWait n hn
    · exact Standard.D'.isFullWait n hn
    · exact Standard.E.isFullWait n hn

theorem orderOne_fullWait_classification (c : Hand 1) (hc : IsFullWait c) :
    IsOrderOneFamily c := by
  have hmem : c ∈ Candidates 1 := by
    apply mem_candidates_iff.mpr
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro i
      exact interior_positive c hc ⟨i.val + 1, by omega⟩
        ⟨by simp, by simp⟩
    · exact IsFullWait.size (by omega) hc
    · omega
  exact orderOne_candidates_classified c hmem hc

theorem orderOne_isFullWait_iff_isOrderOneFamily (c : Hand 1) :
    IsFullWait c ↔ IsOrderOneFamily c := by
  constructor
  · exact orderOne_fullWait_classification c
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Standard.One.a.isFullWait
    · exact Standard.One.b.isFullWait
    · exact Standard.One.c.isFullWait
    · exact Standard.One.c'.isFullWait
    · exact Standard.One.d.isFullWait
    · exact Standard.One.d'.isFullWait

end Mahjong.Hand.Counterexample
