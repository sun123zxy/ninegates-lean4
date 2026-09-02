import Ninegates.Counterexample.EnumSpec
import Ninegates.Wait.Decidable.Basic

/-!
# Elimination of the finite live counterexample candidates

This file contains the computational certificate that no enumerated candidate
is a live counterexample. It uses the enumeration algorithm established in
`EnumSpec` combined with a plain decidable check of `IsLiveFullWait`.

The `native_decide` is used for efficiency.
TODO: allow switching to `decide`.
-/

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
