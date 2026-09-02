import Ninegates.Wait.Basic
import Ninegates.Meldable.Basic

/-!
# Standard full-wait

This file defines the standard full-wait and proves that it is indeed a live full wait.
-/

namespace Mahjong.Hand

@[grind =]
def standardLiveFullWait (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1⟩

@[simp, grind =]
lemma standardLiveFullWait_apply (n : ℕ) (i : Fin (3 * n)) :
    standardLiveFullWait n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1 := by rfl

@[simp, grind =]
lemma size_standardLiveFullWait (n : ℕ) (hn : 0 < n) :
    size (standardLiveFullWait n) = 3 * n + 4 := by
  simp only [size_eq_sum, standardLiveFullWait_apply]
  have hsplit (i : Fin (3 * n)) :
      (if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1) =
        1 + (if i.val = 0 then 2 else 0) +
          (if i.val = 3 * n - 1 then 2 else 0) := by grind
  have hsingle (k : ℕ) (hk : k < 3 * n) :
      (∑ i : Fin (3 * n), if i.val = k then 2 else 0) = 2 := by
    rw [Finset.sum_eq_single ⟨k, hk⟩] <;> grind
  simp [hsplit, Finset.sum_add_distrib, hsingle 0 (by omega), hsingle (3 * n - 1) (by omega)]

theorem IsFullWait.standardLiveFullWait (n : ℕ) (hn : 0 < n) :
    IsFullWait (standardLiveFullWait n) := by
  have mod_three_cases (x : ℕ) : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  intro p
  constructor
  · rw [map_add, size_single, size_standardLiveFullWait]
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
      simp only [standardLiveFullWait_apply, add_apply, pair_apply, single_apply]
      by_cases hi₀ : i.val = 0; · grind
      by_cases hi₁ : i.val = 1; · simp_all; grind
      by_cases hi₂ : i.val = 3 * n - 1; · grind
      have hi₃ : 2 ≤ i.val := by omega
      have hi₄ : i.val ≤ 3 * n - 2 := by omega
      by_cases hi₅ : i.val = p.val; · grind
      rcases mod_three_cases i.val with himod | himod | himod
      all_goals simp_all; grind

theorem IsLiveFullWait.standardLiveFullWait (n : ℕ) (hn : 0 < n) :
    IsLiveFullWait (standardLiveFullWait n) := by
  apply isLiveFullWait_iff_le_three.mpr
  refine ⟨IsFullWait.standardLiveFullWait n hn, ?_⟩
  intro p
  simp only [standardLiveFullWait_apply]
  split_ifs <;> omega

end Mahjong.Hand
