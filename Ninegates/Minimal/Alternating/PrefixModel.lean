/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Defs
public import Ninegates.Meldable.Prefix

/-! A fixed five-rank prefix model and its transport to arbitrary orders. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait.PrefixModel

def value (k : ℕ) : ℤ :=
  if k = 0 then 2 else if k = 1 then 4 else if k = 2 then 6
  else if k = 3 then 3 else if k = 4 then 3 else 0

def winning (draw : Fin 6) (q : Fin 3) : VirtualHand 2 :=
  (fun r ↦ value r.val) + single (n := 2) draw - pair (n := 2) ⟨q.val, by omega⟩

private lemma early_hand {n : ℕ} (order : 2 ≤ n) (i : Rank n) (early : i.val ≤ 4)
    (four : i.val = 4 → n % 2 = 1) : hand n i = value i.val := by
  rw [hand_apply]
  unfold value
  interval_cases position : i.val
  all_goals norm_num
  have not_tail : ¬3 * n ≤ 6 := by have odd := four rfl; omega
  rw [ite_eq_right not_tail, ite_eq_left (four rfl)]

lemma agree {n : ℕ} (order : 2 ≤ n) (i q : Rank n) (small : q.val < 3)
    (limit : ℕ) (bound : limit ≤ 4) (odd : limit = 4 → n % 2 = 1) :
    ∀ k ≤ limit, coefficient (hand n + single i - pair q) (k : ℤ) =
      coefficient (winning ⟨min i.val 5, by omega⟩ ⟨q.val, small⟩) (k : ℤ) := by
  intro k before
  let x : Rank n := ⟨k, by omega⟩
  let y : Rank 2 := ⟨k, by omega⟩
  have actual := coefficient_fin (hand n + single i - pair q) x
  have model := coefficient_fin (winning ⟨min i.val 5, by omega⟩ ⟨q.val, small⟩) y
  change coefficient _ (k : ℤ) = _ at actual model
  rw [actual, model]
  simp only [winning, Pi.sub_apply, Pi.add_apply, pair_apply, single_apply, Fin.ext_iff]
  rw [early_hand order x (by dsimp [x]; omega) (by
    intro at_four
    apply odd
    dsimp [x] at at_four
    omega)]
  dsimp only [x, y]
  split_ifs <;> omega

end Mahjong.VirtualHand.AlternatingWait.PrefixModel
