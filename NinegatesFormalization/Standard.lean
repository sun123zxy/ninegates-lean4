import NinegatesFormalization.Winning
import NinegatesFormalization.Meldable.Basic

namespace Mahjong.Hand

@[grind =]
def standardFullWait (n : ℕ) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1⟩

@[simp, grind =]
lemma standardFullWait_apply (n : ℕ) (i : Fin (3 * n)) :
    standardFullWait n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1 := by rfl

@[simp, grind =]
lemma size_standardFullWait (n : ℕ) (hn : 0 < n) :
    size (standardFullWait n) = 3 * n + 4 := by
  simp only [size_eq_sum, standardFullWait_apply]
  have hsplit (i : Fin (3 * n)) :
      (if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1) =
        1 + (if i.val = 0 then 2 else 0) +
          (if i.val = 3 * n - 1 then 2 else 0) := by grind
  have hsingle (k : ℕ) (hk : k < 3 * n) :
      (∑ i : Fin (3 * n), if i.val = k then 2 else 0) = 2 := by
    rw [Finset.sum_eq_single ⟨k, hk⟩] <;> grind
  simp [hsplit, Finset.sum_add_distrib, hsingle 0 (by omega), hsingle (3 * n - 1) (by omega)]

theorem IsFullWait.standardFullWait (n : ℕ) (hn : 0 < n) :
    IsFullWait (standardFullWait n) := by
  have mod_three_cases (x : ℕ) : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  intro p
  split_ands
  · intro i
    simp only [add_apply, standardFullWait_apply, single_apply]
    split_ifs <;> omega
  · rw [map_add, size_single, size_standardFullWait]
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
      simp only [standardFullWait_apply, add_apply, pair_apply, single_apply]
      by_cases hi₀ : i.val = 0; · grind
      by_cases hi₁ : i.val = 1; · simp_all; grind
      by_cases hi₂ : i.val = 3 * n - 1; · grind
      have hi₃ : 2 ≤ i.val := by omega
      have hi₄ : i.val ≤ 3 * n - 2 := by omega
      by_cases hi₅ : i.val = p.val; · grind
      rcases mod_three_cases i.val with himod | himod | himod
      all_goals simp_all; grind
end Mahjong.Hand
