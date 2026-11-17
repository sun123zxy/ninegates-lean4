/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Consecutive

/-! The two-pair decomposition theorem for full-sided waits, with independent
order and meld count. The exact remainder has one fewer meld. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n} {p q : Rank n}

lemma TwoPair.remainder_meldableWith (h : TwoPair c p q)
    (count : size c = 3 * (m : ℤ) + 1) :
    MeldableWith (m - 1) (c - pair p - pair q) := by
  have remainder_size : size (c - pair p - pair q) = 3 * (m : ℤ) - 3 := by
    simp only [map_sub, size_pair, count]
    ring
  have nonnegative := h.2.nonnegative.size_nonnegative
  rw [remainder_size] at nonnegative
  refine ⟨?_, h.2⟩
  rw [remainder_size]
  omega

/-- Every vertex with an incoming edge lies on a mutual edge, which may be a
self-loop in the fixed class. -/
lemma IsFullWait.incoming_mutual (h : IsFullWait m c) (incoming : ∃ i, DrawPair c i q) :
    ∃ r, DrawPair c q r ∧ DrawPair c r q := by
  obtain ⟨i, hi⟩ := incoming
  obtain ⟨j, hj⟩ := (isFullWait_iff.mp h).2.2 q
  obtain ⟨r, _, _, forward, backward⟩ := hi.consecutive hj
  exact ⟨r, backward, forward⟩

/-- `prp-two-pair` at any used pair in an interchanging class. -/
lemma IsFullWait.twoPair_at (h : IsFullWait m c) (nonfixed : rankClass q ≠ fixedClass c)
    (incoming : ∃ i, DrawPair c i q) :
    ∃ r, TwoPair c q r ∧ MeldableWith (m - 1) (c - pair q - pair r) := by
  obtain ⟨r, forward, backward⟩ := h.incoming_mutual incoming
  have different : q ≠ r := by
    intro equal
    subst r
    exact nonfixed forward.self_fixed_class
  have two := (bidirectional_iff_twoPair different).mp ⟨forward, backward⟩
  exact ⟨r, two, two.remainder_meldableWith h.2.1⟩

/-- Every full-sided wait has a two-pair decomposition, with the two pairs in
the interchanging classes. In particular this rules out full waits with no melds. -/
lemma IsFullWait.exists_twoPair (h : IsFullWait m c) :
    ∃ p q, rankClass p ≠ fixedClass c ∧ rankClass q ≠ fixedClass c ∧
      rankClass p ≠ rankClass q ∧ TwoPair c p q ∧
      MeldableWith (m - 1) (c - pair p - pair q) := by
  have positive : 0 < n := by
    by_contra not_positive
    have zero : n = 0 := by omega
    subst n
    exact not_isFullWait_order_zero m c h
  obtain ⟨i, class_i⟩ := exists_rankClass positive (fixedClass c + 1)
  have i_nonfixed : rankClass i ≠ fixedClass c := by rw [class_i]; simp
  obtain ⟨q, edge⟩ := (isFullWait_iff.mp h).2.2 i
  have q_nonfixed : rankClass q ≠ fixedClass c :=
    fun equal ↦ i_nonfixed (edge.fixed_class_iff.mpr equal)
  obtain ⟨p, two, remainder⟩ := h.twoPair_at q_nonfixed ⟨i, edge⟩
  have p_nonfixed : rankClass p ≠ fixedClass c :=
    fun equal ↦ q_nonfixed (two.drawPair.fixed_class_iff.mpr equal)
  exact ⟨q, p, q_nonfixed, p_nonfixed, two.drawPair.nonfixed_classes q_nonfixed, two, remainder⟩

end Mahjong.VirtualHand
