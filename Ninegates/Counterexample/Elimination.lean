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
# Elimination of the finite live counterexample candidates

This file contains the computational certificate that no enumerated candidate
is a live counterexample. It uses the enumeration algorithm established in
`EnumSpec` combined with a plain decidable check of `IsLiveFullWait`.

The `native_decide` is used. The `meta import`s make the enumeration and decision
procedures available for compile-time execution of the certificate.
-/

@[expose] public section

namespace Mahjong.Hand.Counterexample

theorem minimalCandidates_no_liveCE (n : Nat) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    ∀ c ∈ MinimalCandidates n, ¬ IsLiveCE c := by
  have hcertificate :
      (MinimalCandidates n).all (fun c => decide (¬ IsLiveCE c)) = true := by
    interval_cases n <;> native_decide
  intro c hc
  have hdecide := List.all_eq_true.mp hcertificate c hc
  exact of_decide_eq_true hdecide

end Mahjong.Hand.Counterexample
