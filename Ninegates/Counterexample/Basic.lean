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
## Basic definitions for counterexamples
-/

@[expose] public section

namespace Mahjong.Hand.Counterexample

-- Need to settle on what are the positive examples first.
-- abbrev IsCE {n : ℕ} (c : Hand n) : Prop :=
--   IsFullWait c ∧ c ≠ standardLiveFullWait n

-- abbrev HasCE (n : ℕ) : Prop :=
--   ∃ c : Hand n, IsCE c

abbrev IsLiveCE {n : ℕ} (c : Hand n) : Prop :=
  IsLiveFullWait c ∧ c ≠ standardLiveFullWait n

abbrev HasLiveCE (n : ℕ) : Prop :=
  ∃ c : Hand n, IsLiveCE c

end Mahjong.Hand.Counterexample
