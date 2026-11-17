/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Canonical
public import Ninegates.Meldable.Recovery

/-!
# The linear criterion for virtual meldability

Equal class sizes give a virtual sequence placement. If class sizes are merely
congruent modulo three, subtract integer multiples of triplets at one rank in
each of two classes to make them equal. This constructs a virtual meld
placement without enumerating hands or solving a bounded instance.
-/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

private lemma virtuallyMeldable_of_classSizes (c : VirtualHand n) (positive : 0 < n)
    (classes : (classSize 0 c : ZMod 3) = (classSize 1 c : ZMod 3) ∧
      (classSize 1 c : ZMod 3) = (classSize 2 c : ZMod 3)) : VirtuallyMeldable c := by
  let i0 : Rank n := ⟨2, by omega⟩
  let i1 : Rank n := ⟨0, by omega⟩
  have ci0 : rankClass i0 = 0 := by
    change (3 : ZMod 3) = 0
    exact ZMod.natCast_self 3
  have ci1 : rankClass i1 = 1 := rfl
  let q0 : ℤ := (classSize 0 c - classSize 2 c) / 3
  let q1 : ℤ := (classSize 1 c - classSize 2 c) / 3
  have rem0 : classSize 0 c % 3 = classSize 2 c % 3 := by
    simpa using (ZMod.intCast_eq_intCast_iff' _ _ 3).mp (classes.1.trans classes.2)
  have rem1 : classSize 1 c % 3 = classSize 2 c % 3 := by
    simpa using (ZMod.intCast_eq_intCast_iff' _ _ 3).mp classes.2
  have cancel0 : 3 * q0 = classSize 0 c - classSize 2 c := by dsimp [q0]; omega
  have cancel1 : 3 * q1 = classSize 1 c - classSize 2 c := by dsimp [q1]; omega
  let trips : VirtualHand n := q0 • single i0 + q1 • single i1
  have corrected (r : ZMod 3) : classSize r (c - (3 : ℤ) • trips) =
      classSize r c - 3 * (q0 * (if (0 : ZMod 3) = r then 1 else 0) +
        q1 * (if (1 : ZMod 3) = r then 1 else 0)) := by
    dsimp [trips]
    rw [map_sub, map_smul, map_add, map_smul, map_smul, classSize_single, classSize_single]
    simp only [ci0, ci1, smul_eq_mul]
  have h01 : (0 : ZMod 3) ≠ 1 := by decide +kernel
  have h02 : (0 : ZMod 3) ≠ 2 := by decide +kernel
  have h12 : (1 : ZMod 3) ≠ 2 := by decide +kernel
  have balanced : classSize 0 (c - (3 : ℤ) • trips) = classSize 1 (c - (3 : ℤ) • trips) ∧
      classSize 1 (c - (3 : ℤ) • trips) = classSize 2 (c - (3 : ℤ) • trips) := by
    simp only [corrected]
    simp [h01, h02, h12]
    omega
  obtain ⟨s, equal⟩ := (virtuallySequential_iff_classSizes _).mpr balanced
  refine ⟨⟨s, trips⟩, ?_⟩
  rw [Placement.toHand_eq]
  change sequenceHand s + (3 : ℤ) • trips = c
  rw [equal, sub_add_cancel]

/-- The congruence-class criterion in `prp-canonical-meld-placement`. -/
lemma virtuallyMeldable_iff_classSizes (c : VirtualHand n) : VirtuallyMeldable c ↔
    (classSize 0 c : ZMod 3) = (classSize 1 c : ZMod 3) ∧
      (classSize 1 c : ZMod 3) = (classSize 2 c : ZMod 3) := by
  constructor
  · intro meldable
    exact (classSizes_congruent_iff c).mpr ⟨meldable.size_cast, meldable.rankSum_cast⟩
  · intro classes
    by_cases positive : 0 < n
    · exact virtuallyMeldable_of_classSizes c positive classes
    · have zero : n = 0 := by omega
      subst n
      refine ⟨⟨0, 0⟩, ?_⟩
      ext i
      exact Fin.elim0 i

lemma virtuallyMeldable_iff_size_rankSum (c : VirtualHand n) : VirtuallyMeldable c ↔
    (size c : ZMod 3) = 0 ∧ (rankSum c : ZMod 3) = 0 :=
  (virtuallyMeldable_iff_classSizes c).trans (classSizes_congruent_iff c)

lemma VirtuallyMeldable.classSize_cast_eq {c : VirtualHand n} (h : VirtuallyMeldable c)
    (r s : ZMod 3) : (classSize r c : ZMod 3) = (classSize s c : ZMod 3) := by
  have same := (virtuallyMeldable_iff_classSizes c).mp h
  have classes : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide +kernel
  rcases classes r with rfl | rfl | rfl <;> rcases classes s with rfl | rfl | rfl <;> simp_all

lemma exists_unique_canonical_iff (c : VirtualHand n) :
    (∃! p : Placement n, p.Canonic ∧ p.toHand = c) ↔
      (size c : ZMod 3) = 0 ∧ (rankSum c : ZMod 3) = 0 := by
  constructor
  · rintro ⟨p, ⟨_, equal⟩, _⟩
    exact (virtuallyMeldable_iff_size_rankSum c).mp ⟨p, equal⟩
  · intro congruences
    exact ((virtuallyMeldable_iff_size_rankSum c).mpr congruences).unique_canonical

end Mahjong.VirtualHand
