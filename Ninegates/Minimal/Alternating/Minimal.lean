/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Boundary
public import Ninegates.Minimal.Alternating.Exceptional
public import Ninegates.Minimal.Criterion
public import Ninegates.Minimal.Double.Minimal

/-! Minimality of the alternating families and the improved lower bound. -/

@[expose] public section

namespace Mahjong.VirtualHand
namespace AlternatingWait

private lemma covers {n : ℕ} (r : Fin (3 * n - 2)) (k : Rank n)
    (lower : r.val ≤ k.val) (upper : k.val ≤ r.val + 2) : sequence r k = 1 := by
  simp only [sequence, Pi.add_apply, single_apply, Fin.ext_iff]
  split_ifs <;> omega

lemma no_triplet_removal {n : ℕ} (order : 2 ≤ n) (k : Rank n) :
    ¬IsFullWait (meldCount n - 1) (hand n - triplet k) := by
  by_cases small : hand n k < 3
  · intro smaller
    have impossible := smaller.1 k
    change 0 ≤ hand n k - triplet k k at impossible
    simp only [triplet_apply, single_self] at impossible
    omega
  · have lower : 1 ≤ k.val := by
      by_contra not_positive
      have zero : k.val = 0 := by omega
      simp only [hand_apply, zero, ite_true] at small
      omega
    have upper : k.val < 3 * n - 2 := by
      by_contra tail
      have at_tail : hand n k = 2 := by
        rw [hand_apply]
        split_ifs <;> omega
      omega
    by_cases early : k.val < 4 + n % 2
    · let i : Rank n := ⟨prefixTripletDraw (n % 2) k.val, by
        unfold prefixTripletDraw
        split_ifs <;> omega⟩
      apply not_full_sub_triplet_of_canonical k i
      intro q edge
      by_cases exceptional : n % 2 = 0 ∧ k.val = 2
      · have critical := even_third_triplet_zero order exceptional.1 i q
          (by simp [i, prefixTripletDraw, exceptional.1, exceptional.2]) edge
        have index : k = ⟨2, by omega⟩ := Fin.ext exceptional.2
        simpa only [← index] using critical
      · have later : 4 ≤ i.val := by
          dsimp only [i]
          unfold prefixTripletDraw
          split_ifs <;> omega
        exact prefix_triplet_zero order i q k lower early rfl
          (pair_lt_three order later edge) edge
    · by_cases parity : (k.val + n % 2) % 2 = 0
      · let i : Rank n := ⟨k.val + 3, by omega⟩
        exact not_full_sub_triplet_of_canonical k i
          (fun q edge ↦ five_triplet_zero order i q k (by omega) upper parity rfl edge)
      · let i : Rank n := ⟨k.val - 1, by have := k.isLt; omega⟩
        exact not_full_sub_triplet_of_canonical k i
          (fun q edge ↦ (four_triplet_zero order i q k (by omega) upper (by omega)
            (by dsimp [i]; omega) edge).1)

lemma no_sequence_removal {n : ℕ} (order : 2 ≤ n) (r : Fin (3 * n - 2)) :
    ¬IsFullWait (meldCount n - 1) (hand n - sequence r) := by
  have bound := r.isLt
  by_cases early : r.val < 4 + n % 2
  · let i : Rank n := ⟨prefixSequenceDraw (n % 2) r.val, by
      unfold prefixSequenceDraw
      split_ifs <;> omega⟩
    apply not_full_sub_sequence_of_canonical r i
    intro q edge
    by_cases exceptional : n % 2 = 0 ∧ r.val = 2
    · have critical := even_third_sequence_obstruction order exceptional.1 i q
        (by simp [i, prefixSequenceDraw, exceptional.1, exceptional.2]) edge
      refine ⟨?_, ⟨3, by omega⟩, covers r _ (by dsimp; omega) (by dsimp; omega), critical.2⟩
      simpa only [exceptional.2] using critical.1
    · have later : 4 ≤ i.val := by
        dsimp only [i]
        unfold prefixSequenceDraw
        split_ifs <;> omega
      exact prefix_sequence_obstruction order r i q early rfl
        (pair_lt_three order later edge) edge
  · by_cases parity : (r.val + n % 2) % 2 = 0
    · let i : Rank n := ⟨r.val, by omega⟩
      let k : Rank n := ⟨r.val + 1, by omega⟩
      apply not_full_sub_sequence_of_canonical r i
      intro q edge
      have critical := four_triplet_zero order i q k (by dsimp [k]; omega)
        (by dsimp [k]; omega) (by dsimp [k]; omega) rfl edge
      exact ⟨critical.2, k, covers r k (by dsimp [k]; omega) (by dsimp [k]; omega), critical.1⟩
    · let i : Rank n := ⟨r.val + 2, by omega⟩
      let k : Rank n := ⟨r.val, by omega⟩
      apply not_full_sub_sequence_of_canonical r i
      intro q edge
      have critical := four_sequence_zero order i q k (by dsimp [k]; omega) bound
        (by dsimp [k]; omega) rfl edge
      exact ⟨critical.1, k, covers r k le_rfl (by dsimp [k]; omega), critical.2⟩

lemma minimal {n : ℕ} (order : 2 ≤ n) : IsMinimalFullWait (meldCount n) (hand n) :=
  (full order).minimal_of_no_elementary_removal (no_triplet_removal order)
    (no_sequence_removal order)

lemma even_minimal (a : ℕ) : IsMinimalFullWait (9 * a + 6) (even a) := by
  have count : meldCount (2 * a + 2) = 9 * a + 6 := by unfold meldCount; omega
  simpa only [even, count] using minimal (n := 2 * a + 2) (by omega)

lemma odd_minimal (a : ℕ) : IsMinimalFullWait (9 * a + 10) (odd a) := by
  have count : meldCount (2 * a + 3) = 9 * a + 10 := by unfold meldCount; omega
  simpa only [odd, count] using minimal (n := 2 * a + 3) (by omega)

end AlternatingWait

lemma maxMinimalMeldCount_ge_alternating {n : ℕ} (positive : 0 < n) :
    9 * n / 2 - 3 ≤ maxMinimalMeldCount n := by
  by_cases order : 2 ≤ n
  · exact (AlternatingWait.minimal order).le_max
  · have one : n = 1 := by omega
    subst n
    norm_num

lemma maxMinimalMeldCount_strong_bounds {n : ℕ} (positive : 0 < n) :
    max (2 * n) (9 * n / 2 - 3) ≤ maxMinimalMeldCount n ∧
      maxMinimalMeldCount n < 8 * n :=
  ⟨max_le (maxMinimalMeldCount_ge_two_order positive)
    (maxMinimalMeldCount_ge_alternating positive), maxMinimalMeldCount_lt_eight_order positive⟩

end Mahjong.VirtualHand
