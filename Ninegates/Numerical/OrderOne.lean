/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.OrderOne
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.NatCard

/-! Exact order-one counts for every meld count, obtained by a bijection
with natural compositions and stars and bars. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma orderOne_fullWait_card (m : ℕ) :
    Nat.card {c : VirtualHand 1 // IsFullWait m c} = (3 * m - 2).choose 2 := by
  by_cases order : 2 ≤ m
  · rw [Nat.card_congr (OrderOne.fullWaitEquiv order).symm,
      Nat.card_congr (Sym.equivNatSumOfFintype (Rank 1) (3 * m - 4)).symm,
      Sym.natCard_sym_eq_choose]
    simp only [Nat.card_fin]
    have top : 3 * 1 + (3 * m - 4) - 1 = 3 * m - 2 := by omega
    rw [top]
    exact Nat.choose_symm_of_eq_add (by omega)
  · let : IsEmpty {c : VirtualHand 1 // IsFullWait m c} := ⟨fun c ↦ by
      have lower := c.property.meldCount_gt_order
      omega⟩
    rw [Nat.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega)]

end Mahjong.VirtualHand
