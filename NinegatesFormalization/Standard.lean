import NinegatesFormalization.Winning
import NinegatesFormalization.Meldable.Basic

namespace Mahjong.Hand

@[grind =]
def standardFullWait (n : ℕ) (hn : 0 < n) : Hand n :=
  ⟨fun i ↦ if i = ⟨0, by omega⟩ ∨ i = ⟨3 * n - 1, by omega⟩ then 3 else 1⟩

lemma size_standardFullWait (n : ℕ) (hn : 0 < n) :
    size (standardFullWait n hn) = 3 * n + 4 := by
  change (∑ i : Fin (3 * n), if i = ⟨0, by omega⟩ ∨
      i = ⟨3 * n - 1, by omega⟩ then 3 else 1) = 3 * n + 4
  classical
  let z : Fin (3 * n) := ⟨0, by omega⟩
  let l : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hzl : z ≠ l := by simp [z, l, Fin.ext_iff]; omega
  have hsplit (i : Fin (3 * n)) :
      (if i = z ∨ i = l then 3 else 1) =
        1 + (if i = z then 2 else 0) + (if i = l then 2 else 0) := by
    by_cases hz : i = z <;> by_cases hl : i = l <;> simp_all
  change (∑ i : Fin (3 * n), if i = z ∨ i = l then 3 else 1) = 3 * n + 4
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Fintype.card_fin]

@[simp, grind =]
lemma standardFullWait_apply (n : ℕ) (hn : 0 < n) (i : Fin (3 * n)) :
    standardFullWait n hn i = if i = ⟨0, by omega⟩ ∨ i = ⟨3 * n - 1, by omega⟩ then 3 else 1 := by
  rfl

theorem IsFullWait.standardFullWait (n : ℕ) (hn : 0 < n) :
    IsFullWait (standardFullWait n hn) := by
  intro p
  split_ands
  · intro i
    change (if i = ⟨0, by omega⟩ ∨ i = ⟨3 * n - 1, by omega⟩ then 3 else 1) +
      (if i = p then 1 else 0) ≤ 4
    split_ifs <;> omega
  · rw [map_add, size_single, size_standardFullWait]
  · have hmod : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by omega
    rcases hmod with h | h | h
    · sorry
    · sorry
    · sorry


end Mahjong.Hand
