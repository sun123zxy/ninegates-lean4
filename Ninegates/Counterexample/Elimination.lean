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
# Finite elimination of full wait candidates

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

theorem orderOne_fullWait_classification_of_candidates :
    ∀ c ∈ Candidates 1, IsFullWait c → IsOrderOneFamily c := by
  have hcertificate :
      (Candidates 1).all
        (fun c => decide (IsFullWait c → IsOrderOneFamily c)) = true := by
    native_decide
  intro c hc hfull
  exact (of_decide_eq_true (List.all_eq_true.mp hcertificate c hc)) hfull


end Mahjong.Hand.Counterexample
