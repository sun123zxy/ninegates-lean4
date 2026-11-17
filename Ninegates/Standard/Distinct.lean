/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Basic
public import Ninegates.Standard.OneDefs

/-! Distinctness of the eight standard families and the six order-one hands. -/

@[expose] public section

namespace Mahjong.VirtualHand.Standard

private lemma boundary_values {n : ℕ} (order : 2 ≤ n) (k : Fin 8) :
    (Eight n k ⟨0, by omega⟩, Eight n k ⟨3 * n - 1, by omega⟩,
      Eight n k ⟨1, by omega⟩) =
      ![(3, 3, 1), (3, 0, 1), (0, 3, 1), (1, 0, 1),
        (0, 1, 3), (0, 0, 1), (0, 0, 3), (0, 0, 1)] k := by
  fin_cases k
  all_goals
    norm_num [Eight, A_apply, B_apply order, C_apply order, D_apply order, E_apply order,
      B', C', D', reverse_apply, Fin.val_rev]
    all_goals omega

private lemma D_ne_E {n : ℕ} (order : 2 ≤ n) : D n ≠ E n := by
  intro equal
  have fourth := congrFun equal (⟨3, by omega⟩ : Rank n)
  rw [D_apply order, E_apply order] at fourth
  norm_num at fourth
  split_ifs at fourth <;> omega

lemma Eight_injective {n : ℕ} (order : 2 ≤ n) : Function.Injective (Eight n) := by
  intro i j equal
  have same := congrArg (fun c : VirtualHand n ↦
    (c ⟨0, by omega⟩, c ⟨3 * n - 1, by omega⟩, c ⟨1, by omega⟩)) equal
  rw [boundary_values order i, boundary_values order j] at same
  fin_cases i <;> fin_cases j
  all_goals norm_num at same
  all_goals norm_num
  all_goals
    have different := D_ne_E order
    simp only [Eight] at equal
    tauto

lemma eightFamily_iff_exists {n : ℕ} (c : VirtualHand n) :
    EightFamily c ↔ ∃ k, c = Eight n k := by
  simp [EightFamily, Eight, Fin.exists_fin_succ]

lemma One_injective : Function.Injective One := by decide +kernel

end Mahjong.VirtualHand.Standard
