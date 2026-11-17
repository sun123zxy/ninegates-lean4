/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Graph
public import Ninegates.Meldable.Preserve

/-! Two consecutive edges force a bidirectional edge at an intermediate rank.
The proof follows the moving tile until its canonical triplet appears; earlier
steps preserve the triplet of the middle vertex. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma DrawPair.consecutive_class {c : VirtualHand n} {i q j : Rank n}
    (hi : DrawPair c i q) (hj : DrawPair c q j) : rankClass i = rankClass j := by
  have first := hi.congruence
  have second := hj.congruence
  linear_combination first - second

private lemma consecutive_right_aux (distance : ℕ) :
    ∀ {c : VirtualHand n} {i q j : Rank n}, j.val - i.val = distance → i.val ≤ j.val →
      DrawPair c i q → DrawPair c q j →
      ∃ r : Rank n, (i.val ≤ r.val ∧ r.val ≤ j.val) ∧ rankClass r = rankClass i ∧
        DrawPair c r q ∧ DrawPair c q r := by
  induction distance using Nat.strong_induction_on with
  | h distance ih =>
    intro c i q j length order hi hj
    by_cases equal : i = j
    · subst j
      exact ⟨i, ⟨le_rfl, le_rfl⟩, rfl, hi, hj⟩
    let hands (k : Rank n) := c + single q + single k
    have moving (k a : Rank n) : moveTile (hands k) k a = hands a := by
      dsimp [hands, moveTile]
      abel
    have edge_at (k : Rank n) (actual : Meldable (hands k)) :
        DrawPair c k q ↔ 1 ≤ canonicalTriplet (hands k) q := by
      have commute : c + single k + single q = hands k := by dsimp [hands]; abel
      have reordered : Meldable (c + single k + single q) := by rwa [commute]
      simpa only [commute] using (drawPair_iff_triplet reordered)
    have initial : Meldable (hands i) := by
      have commute : c + single i + single q = hands i := by dsimp [hands]; abel
      rw [← commute]
      exact hi.augmented_meldable
    have initial_pair := (edge_at i initial).mp hi
    by_cases available : 1 ≤ canonicalTriplet (hands i) i
    · exact ⟨i, ⟨le_rfl, order⟩, rfl, hi,
        (drawPair_iff_triplet (i := q) (j := i) initial).mpr available⟩
    have empty : canonicalTriplet (hands i) i = 0 := by
      have nonnegative := initial.canonicalTriplet_nonnegative i
      omega
    have same := (rankClass_eq_iff i j).mp (hi.consecutive_class hj)
    have far : i.val + 3 ≤ j.val := by
      have different : i.val ≠ j.val := fun h ↦ equal (Fin.ext h)
      omega
    let r : Moving.Start n := ⟨i.val, by have := j.isLt; omega⟩
    let next := Moving.rankAt r 3
    have terminal : Meldable (moveTile (hands i) (Moving.rankAt r 0) j) := by
      change Meldable (moveTile (hands i) i j)
      rw [moving]
      exact hj.augmented_meldable
    have moved := Moving.meldable_right_of_long initial r j (by dsimp [r]; omega) terminal
    have step : Moving.right (hands i) r = hands next := by
      change moveTile (hands i) i next = hands next
      exact moving i next
    have next_actual : Meldable (hands next) := by rwa [step] at moved
    have monotone := Moving.canonicalTriplet_right_mono initial r empty moved q
    rw [step] at monotone
    have next_edge : DrawPair c next q := (edge_at next next_actual).mpr (by omega)
    have next_val : next.val = i.val + 3 := by simp [next, r]
    obtain ⟨a, bounds, class_a, forward, backward⟩ := ih (j.val - next.val)
      (by omega) rfl (by omega) next_edge hj
    have class_next : rankClass next = rankClass i := by rw [rankClass_eq_iff]; omega
    exact ⟨a, ⟨by omega, bounds.2⟩, class_a.trans class_next, forward, backward⟩

/-- `prp-consecutive-edges`, including the possibility that the witness is the
middle vertex itself and the resulting mutual edge is a self-loop. -/
lemma DrawPair.consecutive {c : VirtualHand n} {i q j : Rank n}
    (hi : DrawPair c i q) (hj : DrawPair c q j) :
    ∃ r : Rank n, (min i.val j.val ≤ r.val ∧ r.val ≤ max i.val j.val) ∧
      rankClass r = rankClass i ∧ DrawPair c r q ∧ DrawPair c q r := by
  by_cases order : i.val ≤ j.val
  · simpa only [min_eq_left order, max_eq_right order] using
      consecutive_right_aux (j.val - i.val) rfl order hi hj
  · have reflected_order : i.rev.val ≤ j.rev.val := by simp only [Fin.val_rev]; omega
    obtain ⟨r, bounds, same, forward, backward⟩ :=
      consecutive_right_aux (j.rev.val - i.rev.val) rfl reflected_order hi.reverse hj.reverse
    refine ⟨r.rev, ?_, ?_, ?_, ?_⟩
    · have ir := i.isLt
      have jr := j.isLt
      have rr := r.isLt
      simp only [Fin.val_rev] at bounds ⊢
      omega
    · simpa using rankClass_rev_eq same
    · simpa using forward.reverse
    · simpa using backward.reverse

end Mahjong.VirtualHand
