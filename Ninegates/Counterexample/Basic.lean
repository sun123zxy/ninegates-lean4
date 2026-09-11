/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Basic
public import Ninegates.Standard
public import Ninegates.Wait.Basic

/-!
## Counterexamples to the classification of full waits

A counterexample is a full wait outside the eight standard families. The reduction
argument uses these predicates at orders at least two; liveness is not part of either
definition. Order-one classification uses the six standard hands separately.
-/

@[expose] public section

namespace Mahjong.Hand.Counterexample

/-- A full wait outside the eight standard families. -/
abbrev IsCE {n : ℕ} (c : Hand n) : Prop :=
  IsFullWait c ∧ ¬ IsEightFamily c

/-- There exists a full wait outside the eight standard families. -/
abbrev HasCE (n : ℕ) : Prop :=
  ∃ c : Hand n, IsCE c

end Mahjong.Hand.Counterexample
