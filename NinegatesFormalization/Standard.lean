import NinegatesFormalization.Winning
import NinegatesFormalization.Meldable.Basic

namespace Mahjong.Hand

@[grind =]
def standardFullWait (n : ℕ) (hn : 0 < n) : Hand n :=
  Hand.ofFn fun i ↦ if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1

lemma size_standardFullWait (n : ℕ) (hn : 0 < n) :
    size (standardFullWait n hn) = 3 * n + 4 := by
  simp [standardFullWait, size]
  sorry

theorem standardFullWait_apply_fin (n : ℕ) (hn : 0 < n) (i : Fin (3 * n)) :
    standardFullWait n hn i = if i = ⟨0, by omega⟩ ∨ i = ⟨3 * n - 1, by omega⟩ then 3 else 1 := by
  grind

theorem IsFullWait.standardFullWait (n : ℕ) (hn : 0 < n) : IsFullWait (standardFullWait n hn) := by
  have hn' : 0 < 3 * n := by omega
  have hn'' : 3 * n - 1 < 3 * n := by omega
  intro p
  -- case study modulo 3
  split_ands
  · intro; grind
  · rw [map_add, size_single, size_standardFullWait]
  · have hmod : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by omega
    rcases hmod with (h | h | h)
    · -- standardwait - the pair (at 3n-1) - the triplet (at 0)
      let tsm : Hand n := .ofFn fun i ↦ if i = ⟨0, by omega⟩ then 0 else 1
      -- standardwait - the pair (at 3n-1)
      let sm : Hand n := .ofFn fun i ↦ if i = ⟨0, by omega⟩ then 3 else 1
      -- standard wait + winning tile - the pair
      let tm : Hand n := tsm + Hand.single p
      have tsm_apply_fin (i : Fin (3 * n)) : tsm i = if i = ⟨0, by omega⟩ then 0 else 1 := by grind
      have tsm_apply (i : ℤ) : tsm i = if 0 < i ∧ i < 3 * n then 1 else 0 := by grind
      have sm_apply_fin (i : Fin (3 * n)) : sm i = if i = ⟨0, by omega⟩ then 3 else 1 := by grind
      have tsm_plus : tsm + Hand.triplet ⟨0, by omega⟩ = sm := by
        apply Hand.ext_fin; intro i
        rw [add_apply, tsm_apply_fin, Hand.triplet_apply_fin, sm_apply_fin]
        grind
      have sm_plus : sm + pair ⟨3 * n - 1, by omega⟩ = Hand.standardFullWait n hn := by
        apply Hand.ext_fin; intro i
        rw [add_apply, sm_apply_fin, Hand.pair_apply_fin, standardFullWait_apply_fin]
        grind
      use sm + Hand.single p, ⟨3 * n - 1, by omega⟩
      split_ands
      · suffices h : Meldable tm by
          have h' := Meldable.add h (.triplet : Meldable (Hand.triplet ⟨0, by omega⟩))
          unfold tm at h'
          grind
        let tm_witness : Meldable.Placement n := .ofFn 0
          fun i ↦ if i = ⟨p, by omega⟩ ∨ i.val % 3 = 1 then 1 else 0
        -- have tmw_apply (i : Fin (3 * n)) : tm_witness i =
        use tm_witness
        apply Hand.ext; intro i hil hir
        rw [Meldable.Placement.toHand_apply]
        unfold tm; rw [add_apply, tsm_apply, single_apply]
        unfold tm_witness
        -- switch to Z
        repeat rw [Meldable.Placement.tripNum_ofFn]
        repeat rw [Meldable.Placement.seqNum_ofFn]
        simp only [Pi.zero_apply, dite_eq_ite, ite_self, mul_zero, Fin.mk.injEq, zero_add,
          Int.sub_nonneg, Order.sub_one_lt_iff, Int.pred_toNat]
        sorry
      · rw [← sm_plus]; grind
    · sorry
    · sorry


end Mahjong.Hand
