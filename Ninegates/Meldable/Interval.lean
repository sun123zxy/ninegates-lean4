/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Moving

/-! Long tile moves factor into steps of length three. Hence the reachable
ranks form an interval within a congruence class, as in the rewritten paper. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma VirtuallyMeldable.moveTile_rankClass {c : VirtualHand n} (hc : VirtuallyMeldable c)
    {i j : Rank n} (hj : VirtuallyMeldable (moveTile c i j)) : rankClass i = rankClass j := by
  have total := hj.rankSum_cast
  simp only [moveTile, map_add, map_sub, rankSum_single, Int.cast_add, Int.cast_sub] at total
  rw [hc.rankSum_cast] at total
  change (rank i : ZMod 3) = (rank j : ZMod 3)
  linear_combination -total

lemma Meldable.moveTile_right_steps {c : VirtualHand n} (hc : Meldable c)
    (i j k : Rank n) (t : ℕ) (steps : k.val = i.val + 3 * t) (before : k.val ≤ j.val)
    (hj : Meldable (moveTile c i j)) : Meldable (moveTile c i k) := by
  induction t generalizing c i with
  | zero =>
    have same : k = i := Fin.ext (by omega)
    simpa [same] using hc
  | succ t ih =>
    let r : Moving.Start n := ⟨i.val, by have := k.isLt; omega⟩
    let next := Moving.rankAt r 3
    have first : Meldable (moveTile c i next) := by
      exact Moving.meldable_right_of_long hc r j (by dsimp [r]; omega) hj
    have rest : Meldable (moveTile (moveTile c i next) next k) := by
      apply ih first next
      · dsimp [next, Moving.rankAt, r]
        omega
      · simpa using hj
    simpa using rest

lemma Meldable.moveTile_between_right {c : VirtualHand n} (hc : Meldable c)
    {i j k : Rank n} (hj : Meldable (moveTile c i j))
    (left : i.val ≤ k.val) (right : k.val ≤ j.val) (same : rankClass k = rankClass i) :
    Meldable (moveTile c i k) := by
  have congruent := (rankClass_eq_iff k i).mp same
  apply hc.moveTile_right_steps i j k ((k.val - i.val) / 3) _ right hj
  omega

lemma Meldable.moveTile_between_left {c : VirtualHand n} (hc : Meldable c)
    {i j k : Rank n} (hj : Meldable (moveTile c i j))
    (left : j.val ≤ k.val) (right : k.val ≤ i.val) (same : rankClass k = rankClass i) :
    Meldable (moveTile c i k) := by
  have endpoint : Meldable (moveTile (VirtualHand.reverse c) i.rev j.rev) := by
    simpa using hj.reverse
  have intermediate := hc.reverse.moveTile_between_right endpoint
    (show i.rev.val ≤ k.rev.val by simp only [Fin.val_rev]; omega)
    (show k.rev.val ≤ j.rev.val by simp only [Fin.val_rev]; omega)
    (rankClass_rev_eq same)
  simpa using intermediate.reverse

/-- `prp-meldable-tile-moving-interval`: all intermediate ranks in the source
congruence class are reachable. The source need not be separately assumed
positive: meldability of a distinct endpoint already enforces availability. -/
lemma Meldable.moveTile_interval {c : VirtualHand n} (hc : Meldable c)
    {i j k : Rank n} (hj : Meldable (moveTile c i j))
    (between : min i.val j.val ≤ k.val ∧ k.val ≤ max i.val j.val)
    (same : rankClass k = rankClass i) : Meldable (moveTile c i k) := by
  by_cases order : i.val ≤ j.val
  · simp only [min_eq_left order, max_eq_right order] at between
    exact hc.moveTile_between_right hj between.1 between.2 same
  · have reverse_order : j.val ≤ i.val := by omega
    simp only [min_eq_right reverse_order, max_eq_left reverse_order] at between
    exact hc.moveTile_between_left hj between.1 between.2 same

/-- An endpoint formulation that does not require the original hand itself to
be meldable. It will also apply to incoming intervals in the draw-pair graph. -/
lemma moveTile_interval_of_endpoints {c : VirtualHand n} {i a b k : Rank n}
    (ha : Meldable (moveTile c i a)) (hb : Meldable (moveTile c i b))
    (between : min a.val b.val ≤ k.val ∧ k.val ≤ max a.val b.val)
    (same : rankClass k = rankClass a) : Meldable (moveTile c i k) := by
  have endpoint : Meldable (moveTile (moveTile c i a) a b) := by simpa using hb
  simpa using ha.moveTile_interval endpoint between same

end Mahjong.VirtualHand
