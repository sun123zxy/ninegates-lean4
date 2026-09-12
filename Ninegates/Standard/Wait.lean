/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Standard.Basic
public import Ninegates.Wait.Decidable.Basic
public meta import Ninegates.Standard.Defs
public meta import Ninegates.Wait.Decidable.Basic

/-!
# Full-wait and liveness properties of standard families

General full waits have explicit meld placements; the six order-one hands and the exceptional
`E 2` are checked with `native_decide`, as permitted by this project's soundness policy.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

namespace Standard

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

theorem a.isFullWait : IsFullWait a := by native_decide

theorem a.isLiveFullWait : IsLiveFullWait a := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨a.isFullWait, by decide⟩

theorem b.isFullWait : IsFullWait b := by native_decide

theorem b.isLiveFullWait : IsLiveFullWait b := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨b.isFullWait, by decide⟩

theorem c.isFullWait : IsFullWait c := by native_decide

theorem c.isLiveFullWait : IsLiveFullWait c := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨c.isFullWait, by decide⟩

theorem c'.isFullWait : IsFullWait c' := by native_decide

theorem c'.isLiveFullWait : IsLiveFullWait c' := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨c'.isFullWait, by decide⟩

theorem d.isFullWait : IsFullWait d := by native_decide

theorem d.isLiveFullWait : IsLiveFullWait d := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨d.isFullWait, by decide⟩

theorem d'.isFullWait : IsFullWait d' := by native_decide

theorem d'.isLiveFullWait : IsLiveFullWait d' := by
  apply isLiveFullWait_iff_le_three.mpr
  exact ⟨d'.isFullWait, by decide⟩

end One

end Standard

end Mahjong.Hand
