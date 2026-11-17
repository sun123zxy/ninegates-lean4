/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Classes

/-! At order one every congruence class consists of exactly one rank. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma rankClass_orderOne_injective : Function.Injective (rankClass (n := 1)) := by
  intro i j same
  have residue := (rankClass_eq_iff i j).mp same
  have bound_i := i.isLt
  have bound_j := j.isLt
  exact Fin.ext (by omega)

lemma classSize_orderOne (c : VirtualHand 1) (i : Rank 1) : classSize (rankClass i) c = c i := by
  apply classSize_eq_single i
  intro j same different
  have residue := (rankClass_eq_iff j i).mp same
  have bound_i := i.isLt
  have bound_j := j.isLt
  have equal : j = i := Fin.ext (by omega)
  exact (different equal).elim

namespace OrderOne

/-- One copy in a specified fixed class, and two copies in each other class. -/
def pairThreshold (s : ZMod 3) : VirtualHand 1 := fun i ↦
  if rankClass i = s then 1 else 2

lemma pairThreshold_bounds (s : ZMod 3) (i : Rank 1) :
    1 ≤ pairThreshold s i ∧ pairThreshold s i ≤ 2 := by
  unfold pairThreshold
  split_ifs <;> norm_num

lemma size_pairThreshold (s : ZMod 3) : size (pairThreshold s) = 5 := by
  fin_cases s <;> decide +kernel

lemma rankSum_pairThreshold (s : ZMod 3) : (rankSum (pairThreshold s) : ZMod 3) = -s := by
  fin_cases s <;> decide +kernel

/-- Natural compositions are the nonnegative integer hand vectors of the same size. -/
def naturalHandEquiv (k : ℕ) :
    {q : Rank 1 → ℕ // ∑ i, q i = k} ≃
      {c : VirtualHand 1 // Nonnegative c ∧ size c = (k : ℤ)} where
  toFun q := ⟨fun i ↦ (q.val i : ℤ), fun i ↦ by simp, by
    change (∑ i, (q.val i : ℤ)) = (k : ℤ)
    exact_mod_cast q.property⟩
  invFun c := ⟨fun i ↦ (c.val i).toNat, by
    have equal : ((∑ i, (c.val i).toNat : ℕ) : ℤ) = k := by
      rw [Nat.cast_sum]
      calc
        _ = ∑ i, c.val i := Finset.sum_congr rfl fun i _ ↦ Int.toNat_of_nonneg (c.property.1 i)
        _ = k := c.property.2
    exact_mod_cast equal⟩
  left_inv q := Subtype.ext (by funext i; simp)
  right_inv c := Subtype.ext (by funext i; exact Int.toNat_of_nonneg (c.property.1 i))

end OrderOne

end Mahjong.VirtualHand
