/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Canonical

/-! With only three ranks, nonnegativity and the congruence conditions suffice
for meldability: the single sequence coefficient leaves nonnegative triplets. -/

@[expose] public section

namespace Mahjong.VirtualHand

lemma sequenceHand_orderOne (s : Fin 1 → ℤ) : sequenceHand (n := 1) s = fun _ ↦ s 0 := by
  ext i
  fin_cases i <;> simp [sequenceHand, sequence, single]

lemma VirtuallyMeldable.meldable_orderOne {c : VirtualHand 1} (virtual : VirtuallyMeldable c)
    (positive : Nonnegative c) : Meldable c := by
  obtain ⟨p, ⟨canonical, equal⟩, _⟩ := virtual.unique_canonical
  rw [← equal, canonical.meldable_iff_tripNum_nonnegative]
  intro i
  change 0 ≤ p.tripNum i
  have sequences := canonical 0
  have actual : 0 ≤ c i := positive i
  rw [← equal, Placement.toHand_eq, sequenceHand_orderOne] at actual
  change 0 ≤ p.seqNum 0 + 3 * p.tripNum i at actual
  omega

lemma meldable_orderOne_iff {c : VirtualHand 1} :
    Meldable c ↔ Nonnegative c ∧ VirtuallyMeldable c :=
  ⟨fun h ↦ ⟨h.nonnegative, h.virtuallyMeldable⟩, fun h ↦ h.2.meldable_orderOne h.1⟩

end Mahjong.VirtualHand
