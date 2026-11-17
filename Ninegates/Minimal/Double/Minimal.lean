/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Double.Rigidity
public import Ninegates.Minimal.Maximum

/-! Minimality of `(3,2,...,2)`, giving the lower bound `2n≤M(n)`. -/

@[expose] public section

namespace Mahjong.VirtualHand

namespace DoubleWait

lemma minimal {n : ℕ} (positive : 0 < n) : IsMinimalFullWait (2 * n) (hand n) := by
  refine ⟨full positive, ?_⟩
  intro k remainder removed smaller meldable equal
  obtain ⟨u, positive_u, equal_u⟩ := meldable
  let first : Rank n := ⟨0, by omega⟩
  have extend {i j : Rank n} (edge : DrawPair remainder i j) : DrawPair (hand n) i j := by
    rw [equal]
    exact edge.add_meldable ⟨u, positive_u, equal_u⟩
  have assemble (i j : Rank n) (v : Placement n)
      (equal_v : v.toHand = remainder + single i - pair j) :
      (v.add u).toHand = hand n + single i - pair j := by
    rw [Placement.toHand_add, equal_v, equal_u, equal]
    abel
  obtain ⟨q, edge⟩ := (isFullWait_iff.mp smaller).2.2 first
  have forced := first_draw_pair rfl (extend edge)
  subst q
  obtain ⟨v, positive_v, equal_v⟩ := edge
  have positive_w := positive_v.add positive_u
  have equal_w := assemble first first v equal_v
  have twos : hand n + single first - pair first = fun _ : Rank n ↦ 2 := by
    rw [hand_eq first rfl]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, pair_apply]
    ring
  rw [twos] at equal_w
  have upper : ∀ i, (v.add u).toHand i ≤ 2 := by intro i; rw [equal_w]
  have triplets := positive_w.tripNum_eq_zero_of_hand_le_two upper
  have no_triplets : u.tripNum = 0 := by
    ext i
    have sum_zero := congrFun triplets i
    simp only [Placement.add_tripNum, Pi.add_apply, Pi.zero_apply] at sum_zero
    have nonnegative_v : 0 ≤ v.tripNum i := positive_v.2 i
    have nonnegative_u : 0 ≤ u.tripNum i := positive_u.2 i
    change u.tripNum i = 0
    omega
  have sequences : (v.add u).seqNum = fun r ↦ Periodic.value 2 0 0 r.val := by
    apply sequenceHand_injective
    rw [Periodic.sequenceHand_twos]
    simpa only [Placement.toHand_eq, triplets, smul_zero, add_zero] using equal_w
  have no_sequences : u.seqNum = 0 := by
    ext r
    change u.seqNum r = 0
    have lower : 0 ≤ u.seqNum r := positive_u.1 r
    by_cases block : r.val % 3 = 0
    · let i : Rank n := ⟨r.val + 1, by omega⟩
      obtain ⟨q, edge⟩ := (isFullWait_iff.mp smaller).2.2 i
      obtain ⟨w, positive, equal_w⟩ := edge
      have forbidden := middle_draw_no_block r block (i := i) rfl
        (extend ⟨w, positive, equal_w⟩) (positive.add positive_u) (assemble i q w equal_w)
      simp only [Placement.add_seqNum, Pi.add_apply] at forbidden
      have remaining : 0 ≤ w.seqNum r := positive.1 r
      omega
    · have sum := congrFun sequences r
      simp only [Placement.add_seqNum, Pi.add_apply] at sum
      have remaining : 0 ≤ v.seqNum r := positive_v.1 r
      have residue : (r.val : ℤ) % 3 ≠ 0 := by omega
      simp only [Periodic.value, ite_eq_right residue, ite_self] at sum
      omega
  rw [← equal_u, Placement.toHand_eq, no_sequences, no_triplets, map_zero, smul_zero, add_zero]

end DoubleWait

lemma maxMinimalMeldCount_ge_two_order {n : ℕ} (positive : 0 < n) :
    2 * n ≤ maxMinimalMeldCount n := (DoubleWait.minimal positive).le_max

lemma maxMinimalMeldCount_bounds {n : ℕ} (positive : 0 < n) :
    2 * n ≤ maxMinimalMeldCount n ∧ maxMinimalMeldCount n < 8 * n :=
  ⟨maxMinimalMeldCount_ge_two_order positive, maxMinimalMeldCount_lt_eight_order positive⟩

/-- The paper's coarse bound, including an attaining hand and maximality. -/
lemma exists_maximal_minimal_meldCount {n : ℕ} (positive : 0 < n) :
    ∃ M : ℕ, (∃ c : VirtualHand n, IsMinimalFullWait M c) ∧
      (∀ {m : ℕ} {c : VirtualHand n}, IsMinimalFullWait m c → m ≤ M) ∧
        2 * n ≤ M ∧ M < 8 * n :=
  ⟨maxMinimalMeldCount n, exists_minimal_at_max positive, fun h ↦ h.le_max,
    maxMinimalMeldCount_bounds positive⟩

end Mahjong.VirtualHand
