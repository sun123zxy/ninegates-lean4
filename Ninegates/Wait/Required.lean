/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.PillarRemainder
public import Ninegates.Meldable.RequiredTwo

/-! Required sequence rows of the unique two-pair remainder. In fixed class
two they determine all coefficients and reduce the pillars to four choices. -/

@[expose] public section

namespace Mahjong.VirtualHand.Pillars

variable {n : ℕ} {c : VirtualHand n} {p q : Rank n}

lemma exists_sequence_rows_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) :
    ∃ s : Fin (3 * n - 2) → ℤ, 0 ≤ s ∧ sequenceHand s = c - pair p - pair q ∧
      (∑ j, s j) = (n : ℤ) ∧
      (∀ j ∈ RequiredSequences.row p, 1 ≤ s j) ∧
      (∀ j ∈ RequiredSequences.row q, 1 ≤ s j) := by
  have remainder := pillars.remainder_sequential_moves_succ order full
  obtain ⟨s, positive, equal⟩ := remainder.1
  have count := remainder.2.1
  rw [← equal, size_sequenceHand] at count
  refine ⟨s, positive, equal, by omega, ?_, ?_⟩
  · apply RequiredSequences.row_required positive p
    intro i same
    rw [equal]
    exact remainder.2.2.1 i same
  · apply RequiredSequences.row_required positive q
    intro i same
    rw [equal]
    exact remainder.2.2.2 i same

lemma fixed_two_decomposition_succ (pillars : Pillars c p q) (order : 2 ≤ n)
    (full : IsFullWait (n + 1) c) (fixed : fixedClass c = 2) (class_p : rankClass p = 1) :
    (p.val = 0 ∨ p.val = 3) ∧ (q.val = 3 * n - 4 ∨ q.val = 3 * n - 1) ∧
      c = pair p + pair q + sequenceHand
        (fun j ↦ if j ∈ RequiredSequences.row p ∪ RequiredSequences.row q then 1 else 0) := by
  have class_q : rankClass q = 0 := by
    rw [pillars.class_q, pairedClass, fixed, class_p]
    decide +kernel
  have p_class := (rankClass_eq_one_iff p).mp class_p
  have q_class := (rankClass_eq_zero_iff q).mp class_q
  obtain ⟨s, positive, equal, total, required_p, required_q⟩ :=
    pillars.exists_sequence_rows_succ order full
  have positions := RequiredSequences.pillar_positions_two order positive total p q
    p_class q_class required_p required_q
  have coefficients := RequiredSequences.coefficients_two order positive total p q
    p_class q_class required_p required_q
  refine ⟨positions.1, positions.2, ?_⟩
  rw [← coefficients, equal]
  abel

end Mahjong.VirtualHand.Pillars
