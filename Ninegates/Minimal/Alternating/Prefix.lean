/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Defs
public import Ninegates.Wait.Graph

/-! A later draw in an alternating family must pair among the first three ranks. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

lemma pair_lt_three {n : ℕ} (order : 2 ≤ n) {i q : Rank n} (later : 4 ≤ i.val)
    (edge : DrawPair (hand n) i q) : q.val < 3 := by
  by_contra outside
  let zero : Rank n := ⟨0, by omega⟩
  let one : Rank n := ⟨1, by omega⟩
  let two : Rank n := ⟨2, by omega⟩
  let three : Rank n := ⟨3, by omega⟩
  let d := hand n + single i - pair q
  have unchanged (r : Rank n) (early : r.val ≤ 2) : d r = hand n r := by
    have not_draw : r ≠ i := by intro equal; have := congrArg Fin.val equal; omega
    have not_pair : r ≠ q := by intro equal; have := congrArg Fin.val equal; omega
    simp only [d, Pi.sub_apply, Pi.add_apply, pair_apply, single_of_ne not_draw,
      single_of_ne not_pair, mul_zero, add_zero, sub_zero]
  have inputs : d zero = 2 ∧ d one = 4 ∧ d two = 6 := by
    exact ⟨(unchanged zero (by dsimp [zero]; omega)).trans rfl,
      (unchanged one (by dsimp [one]; omega)).trans rfl,
      (unchanged two (by dsimp [two]; omega)).trans rfl⟩
  have current (k : Rank n) : coefficient d k.val = d k := coefficient_fin d k
  have at_zero : coefficient d (0 : ℤ) = 2 := by
    simpa [zero] using (current zero).trans inputs.1
  have at_one : coefficient d (1 : ℤ) = 4 := by
    simpa [one] using (current one).trans inputs.2.1
  have at_two : coefficient d (2 : ℤ) = 6 := by
    simpa [two] using (current two).trans inputs.2.2
  have first : canonicalSequence d 1 = 2 := by
    rw [canonicalSequence_succ d 0]
    norm_num [at_zero]
  have second : canonicalSequence d 2 = 2 := by
    rw [canonicalSequence_succ d 1, first]
    norm_num [at_one]
  have third : canonicalSequence d 3 = 2 := by
    rw [canonicalSequence_succ d 2, second, first]
    norm_num [at_two]
  have upper : d three ≤ 3 := by
    have no_draw : three ≠ i := by
      intro equal
      have := congrArg Fin.val equal
      dsimp [three] at *
      omega
    have positive_pair : 0 ≤ pair q three := nonnegative_pair q three
    simp only [d, Pi.sub_apply, Pi.add_apply, single_of_ne no_draw]
    have base : hand n three = 3 := rfl
    rw [base]
    omega
  have actual := edge.canonicalTriplet_nonnegative three
  rw [canonicalTriplet_eq] at actual
  change 0 ≤ (d three - canonicalSequence d 3 - canonicalSequence d 2) / 3 at actual
  rw [third, second] at actual
  omega

end Mahjong.VirtualHand.AlternatingWait
