import Ninegates.Counterexample.EnumSpec
import Ninegates.Wait.Decidable.Basic

/-!
# Elimination of the finite live counterexample candidates

This file contains the computational certificate that no enumerated candidate
is a live counterexample.  The certificate uses the ordinary proposition
decidability for `IsLiveCE`, including the short-circuit wait checker.
-/

namespace Mahjong.Hand.Counterexample

/-
No enumerated small candidate is a live counterexample.
The `native_decide` certificate intentionally checks the established
proposition-level definitions directly.
-/
theorem minimalCandidates_no_liveCE (n : Nat) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    ∀ c ∈ MinimalCandidates n, ¬ IsLiveCE c := by
  have hcertificate :
      (MinimalCandidates n).all (fun c => decide (¬ IsLiveCE c)) = true := by
    interval_cases n <;> native_decide
  intro c hc
  have hdecide := List.all_eq_true.mp hcertificate c hc
  exact of_decide_eq_true hdecide

end Mahjong.Hand.Counterexample
