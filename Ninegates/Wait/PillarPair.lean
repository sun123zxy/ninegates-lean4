/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Pillars
public import Ninegates.Wait.TwoPair

/-! The draw-pair graph between the two interchanging classes is forced by
their pillars. Its only nonloop mutual edge gives the unique two-pair decomposition. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n m : ℕ} {c : VirtualHand n} {p q : Rank n}

structure Pillars (c : VirtualHand n) (p q : Rank n) : Prop where
  nonfixed_p : rankClass p ≠ fixedClass c
  class_q : rankClass q = pairedClass c (rankClass p)
  pillar_p : Pillar c p
  pillar_q : Pillar c q

namespace Pillars

lemma nonfixed_q (h : Pillars c p q) : rankClass q ≠ fixedClass c := by
  simpa only [Ne, h.class_q, pairedClass_eq_fixed_iff] using h.nonfixed_p

lemma different_classes (h : Pillars c p q) : rankClass p ≠ rankClass q := by
  rw [h.class_q]
  intro equal
  exact h.nonfixed_p ((pairedClass_eq_self_iff c (rankClass p)).mp equal.symm)

lemma different (h : Pillars c p q) : p ≠ q :=
  fun equal ↦ h.different_classes (congrArg rankClass equal)

lemma swap (h : Pillars c p q) : Pillars c q p where
  nonfixed_p := h.nonfixed_q
  class_q := by rw [h.class_q, pairedClass_pairedClass]
  pillar_p := h.pillar_q
  pillar_q := h.pillar_p

/-- Part (1) of `prp-draw-pair-n-plus-one`, with uniqueness of the pair. -/
lemma drawPair_iff (pillars : Pillars c p q) (full : IsFullWait m c)
    {i j : Rank n} (class_i : rankClass i = rankClass p) : DrawPair c i j ↔ j = q := by
  have unique {j : Rank n} (edge : DrawPair c i j) : j = q := by
    have class_j : rankClass j = rankClass q := by
      rw [edge.class_eq, class_i, pillars.class_q]
    have different : i ≠ j := by
      intro equal
      have classes := edge.nonfixed_classes (by rw [class_i]; exact pillars.nonfixed_p)
      exact classes (congrArg rankClass equal)
    exact pillars.pillar_q.2 j class_j (edge.pair_available different)
  constructor
  · exact unique
  · intro equal
    subst j
    obtain ⟨a, edge⟩ := (isFullWait_iff.mp full).2.2 i
    rwa [unique edge] at edge

lemma twoPair (pillars : Pillars c p q) (full : IsFullWait m c) : TwoPair c p q := by
  apply (bidirectional_iff_twoPair pillars.different).mp
  exact ⟨(pillars.drawPair_iff full rfl).mpr rfl, (pillars.swap.drawPair_iff full rfl).mpr rfl⟩

/-- Part (2) of `prp-draw-pair-n-plus-one`, uniqueness up to exchanging the pairs. -/
lemma twoPair_iff (pillars : Pillars c p q) (order : 2 ≤ n) (full : IsFullWait (n + 1) c)
    (a b : Rank n) : TwoPair c a b ↔ (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  constructor
  · intro two
    have pair_a := two.comm.drawPair.pair_available two.1.symm
    have pair_b := two.drawPair.pair_available two.1
    rcases three_classes_exhaust (fixedClass c) (rankClass p) (rankClass q)
        pillars.nonfixed_p.symm pillars.nonfixed_q.symm pillars.different_classes (rankClass a)
        with fixed | left | right
    · have fixed_b := two.drawPair.fixed_class_iff.mp fixed
      exact (two.1 (full.fixed_pair_unique_succ order fixed fixed_b pair_a pair_b)).elim
    · have a_eq := pillars.pillar_p.2 a left pair_a
      subst a
      exact Or.inl ⟨rfl, (pillars.drawPair_iff full rfl).mp two.drawPair⟩
    · have a_eq := pillars.pillar_q.2 a right pair_a
      subst a
      exact Or.inr ⟨rfl, (pillars.swap.drawPair_iff full rfl).mp two.drawPair⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact pillars.twoPair full
    · exact pillars.swap.twoPair full

end Pillars

lemma IsFullWait.exists_pillars_class (order : 2 ≤ n) (h : IsFullWait (n + 1) c)
    (r : ZMod 3) (nonfixed : r ≠ fixedClass c) :
    ∃ p q : Rank n, Pillars c p q ∧ rankClass p = r := by
  obtain ⟨p, class_p, pillar_p, _⟩ := h.exists_pillar order r nonfixed
  have other_nonfixed : pairedClass c r ≠ fixedClass c := by simpa using nonfixed
  obtain ⟨q, class_q, pillar_q, _⟩ := h.exists_pillar order _ other_nonfixed
  refine ⟨p, q, ⟨by rwa [class_p], ?_, pillar_p, pillar_q⟩, class_p⟩
  simpa only [class_p] using class_q

lemma IsFullWait.exists_pillars (order : 2 ≤ n) (h : IsFullWait (n + 1) c) :
    ∃ p q : Rank n, Pillars c p q := by
  obtain ⟨p, q, pillars, _⟩ := h.exists_pillars_class order (fixedClass c + 1) (by simp)
  exact ⟨p, q, pillars⟩

lemma IsFullWait.exists_unique_twoPair_succ (order : 2 ≤ n) (h : IsFullWait (n + 1) c) :
    ∃ p q : Rank n, Pillars c p q ∧ TwoPair c p q ∧
      ∀ a b, TwoPair c a b → (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  obtain ⟨p, q, pillars⟩ := h.exists_pillars order
  exact ⟨p, q, pillars, pillars.twoPair h, fun a b two ↦ (pillars.twoPair_iff order h a b).mp two⟩

end Mahjong.VirtualHand
