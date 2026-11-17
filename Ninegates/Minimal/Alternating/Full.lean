/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Class
public import Ninegates.Minimal.Alternating.Local
public import Ninegates.Wait.Abundance

/-! Full-sidedness of both alternating families. The abundance estimate covers
all coordinates except their short initial runs of three copies. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

lemma draw_congruence_iff {n : ℕ} (order : 2 ≤ n) (i q : Rank n) :
    rankClass i + rankClass q = -(rankSum (hand n) : ZMod 3) ↔
      (i.val + q.val + n % 2) % 3 = 2 := by
  change (rankClass i + rankClass q = -fixedClass (hand n)) ↔ _
  rw [fixedClass_hand order,
    ← ZMod.natCast_eq_natCast_iff' (i.val + q.val + n % 2) 2 3]
  simp only [rankClass, rank, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
    Nat.cast_ofNat]
  have six : (6 : ZMod 3) = 0 := by decide +kernel
  constructor
  · intro h
    linear_combination h - six
  · intro h
    linear_combination h + six

lemma threshold_after_pair {n : ℕ} (order : 2 ≤ n) (q k : Rank n) (small : q.val < 3)
    (three : k.val ≠ 3) (four : n % 2 = 1 → k.val ≠ 4) :
    abundanceThreshold k - 2 ≤ hand n k - pair q k := by
  have bound := k.isLt
  by_cases early : k.val < 3
  · have sizes : abundanceThreshold k ≤ hand n k := by
      have positions : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
      simp only [abundanceThreshold_apply, hand_apply]
      rcases positions with position | position | position
      all_goals norm_num only [position]; split_ifs <;> norm_num at *
    have pair_bound : pair q k ≤ 2 := by
      simp only [pair_apply, single_apply]
      split_ifs <;> norm_num
    linarith
  · have different : k ≠ q := by intro same; have := congrArg Fin.val same; omega
    rw [pair_apply, single_of_ne different, mul_zero, sub_zero]
    have not_zero : k.val ≠ 0 := by omega
    have not_one : k.val ≠ 1 := by omega
    have not_two : k.val ≠ 2 := by omega
    by_cases tail : 3 * n - 2 ≤ k.val
    · have at_tail : hand n k = 2 := by
        simp only [hand_apply, ite_eq_right not_zero, ite_eq_right not_one,
          ite_eq_right not_two, ite_eq_right three, ite_eq_left tail]
      have near : abundanceThreshold k ≤ 4 := by
        rw [abundanceThreshold_apply]
        split_ifs <;> omega
      rw [at_tail]
      omega
    · have at_middle : 4 ≤ hand n k := by
        have not_special : ¬(n % 2 = 1 ∧ k.val = 4) := by
          rintro ⟨odd, at_four⟩
          exact four odd at_four
        simp only [hand_apply, ite_eq_right not_zero, ite_eq_right not_one,
          ite_eq_right not_two, ite_eq_right three, ite_eq_right tail, ite_eq_right not_special]
        split_ifs <;> norm_num
      have upper := (abundanceThreshold_bounds k).2
      omega

lemma full {n : ℕ} (order : 2 ≤ n) : IsFullWait (meldCount n) (hand n) := by
  have count := size_hand order
  have residue : (size (hand n) : ZMod 3) = 1 := by
    rw [count]
    push_cast
    rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul, zero_add]
  apply isFullWait_iff.mpr
  refine ⟨nonnegative_hand n, count, ?_⟩
  intro i
  let q : Rank n := ⟨(5 - (i.val % 3 + n % 2)) % 3, by omega⟩
  have small : q.val < 3 := by dsimp [q]; omega
  have congruent : (i.val + q.val + n % 2) % 3 = 2 := by dsimp [q]; omega
  have virtual := (virtuallyMeldable_draw_iff residue i q).mpr
    ((draw_congruence_iff order i q).mpr congruent)
  have initial := prefix_triplets_nonnegative order i q small congruent
  refine ⟨q, (meldable_iff_scan _).mpr ⟨virtual, ?_⟩⟩
  intro k
  by_cases three : k.val = 3
  · have same : k = ⟨3, by omega⟩ := Fin.ext three
    simpa only [← same] using initial.1
  · by_cases four : n % 2 = 1 ∧ k.val = 4
    · have same : k = ⟨4, by omega⟩ := Fin.ext four.2
      simpa only [← same] using initial.2 four.1
    · apply virtual.canonicalTriplet_nonnegative_of_threshold
      have bound := threshold_after_pair order q k small three (by
        intro odd at_four
        exact four ⟨odd, at_four⟩)
      have draw : 0 ≤ single i k := nonnegative_single i k
      change abundanceThreshold k - 2 ≤ hand n k + single i k - pair q k
      linarith

lemma even_full (a : ℕ) : IsFullWait (9 * a + 6) (even a) := by
  have count : meldCount (2 * a + 2) = 9 * a + 6 := by unfold meldCount; omega
  simpa only [even, count] using full (n := 2 * a + 2) (by omega)

lemma odd_full (a : ℕ) : IsFullWait (9 * a + 10) (odd a) := by
  have count : meldCount (2 * a + 3) = 9 * a + 10 := by unfold meldCount; omega
  simpa only [odd, count] using full (n := 2 * a + 3) (by omega)

end Mahjong.VirtualHand.AlternatingWait
