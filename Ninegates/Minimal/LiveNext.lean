/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Next
public import Ninegates.Wait.Sharpness
public import Mathlib.SetTheory.Cardinal.Finite

/-! Live nonminimal `(n,n+2)` waits are exactly Nine Gates with one additional
sequence avoiding both boundary ranks. This gives a structural count and shows
that the class-bound sharpness family is minimal as well as live. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma Standard.A_add_sequence_live_iff (order : 2 ≤ n) (r : Fin (3 * n - 2)) :
    IsLiveFullWait 4 (n + 2) (A n + sequence r) ↔
      0 < r.val ∧ r.val + 3 < 3 * n := by
  rw [isLiveFullWait_iff]
  constructor
  · rintro ⟨_, bound⟩
    have first := bound ⟨0, by omega⟩
    have last := bound ⟨3 * n - 1, by omega⟩
    have legal := r.isLt
    simp only [Pi.add_apply, A_apply, sequence_eq_segment, segment_apply] at first last
    split_ifs at first last <;> norm_num at * <;> omega
  · rintro ⟨lower, upper⟩
    refine ⟨by simpa only [Nat.add_assoc] using (A_full order).add_sequence r, ?_⟩
    intro i
    have legal := i.isLt
    simp only [Pi.add_apply, A_apply, sequence_eq_segment, segment_apply]
    split_ifs <;> omega

private lemma standard_eq_A_of_live_add {m : ℕ} (order : 2 ≤ n) (k : Fin 8)
    {d : VirtualHand n} (positive : Nonnegative d)
    (live : IsLiveFullWait 4 m (Standard.Eight n k + d)) :
    Standard.Eight n k = Standard.A n := by
  apply liveFullWait_unique order
  apply isLiveFullWait_iff.mpr
  refine ⟨((Standard.eightFamily_iff_exists _).mpr ⟨k, rfl⟩).full order, ?_⟩
  intro i
  have bound := (isLiveFullWait_iff.mp live).2 i
  have nonnegative : 0 ≤ d i := positive i
  simp only [Pi.add_apply] at bound
  omega

lemma next_live_not_minimal_iff (order : 2 ≤ n) (c : VirtualHand n) :
    (IsLiveFullWait 4 (n + 2) c ∧ ¬IsMinimalFullWait (n + 2) c) ↔
      ∃ r : Fin (3 * n - 2), 0 < r.val ∧ r.val + 3 < 3 * n ∧
        c = Standard.A n + sequence r := by
  constructor
  · rintro ⟨live, nonminimal⟩
    obtain ⟨k, (⟨i, equal⟩ | ⟨r, equal⟩)⟩ :=
      (next_full_not_minimal_iff order c).mp ⟨live.1, nonminimal⟩
    · rw [equal] at live
      have base := standard_eq_A_of_live_add order k (nonnegative_triplet i) live
      rw [base] at live
      have bound := (isLiveFullWait_iff.mp live).2 i
      simp only [Pi.add_apply, triplet_apply, single_self, mul_one] at bound
      rw [Standard.A_apply] at bound
      split_ifs at bound <;> omega
    · rw [equal] at live
      have base := standard_eq_A_of_live_add order k (nonnegative_sequence r) live
      rw [base] at live
      obtain ⟨lower, upper⟩ := (Standard.A_add_sequence_live_iff order r).mp live
      exact ⟨r, lower, upper, equal.trans (by rw [base])⟩
  · rintro ⟨r, lower, upper, rfl⟩
    refine ⟨(Standard.A_add_sequence_live_iff order r).mpr ⟨lower, upper⟩, ?_⟩
    exact ((next_full_not_minimal_iff order _).mpr ⟨0, Or.inr ⟨r, rfl⟩⟩).2

lemma IsLiveFullWait.minimal_next_of_missing_boundary (order : 2 ≤ n)
    {c : VirtualHand n} (live : IsLiveFullWait 4 (n + 2) c)
    (missing : ∃ i : Rank n, (i.val = 0 ∨ i.val + 1 = 3 * n) ∧ c i = 0) :
    IsMinimalFullWait (n + 2) c := by
  by_contra nonminimal
  obtain ⟨r, _, _, equal⟩ := (next_live_not_minimal_iff order c).mp ⟨live, nonminimal⟩
  obtain ⟨i, boundary, zero⟩ := missing
  have at_i := congrFun equal i
  have nonnegative : 0 ≤ sequence r i := nonnegative_sequence r i
  simp only [Pi.add_apply, Standard.A_apply, ite_eq_left boundary, zero] at at_i
  omega

namespace Standard

def nextLiveNonminimal (n : ℕ) (k : Fin (3 * n - 4)) : VirtualHand n :=
  A n + sequence ⟨k.val + 1, by have bound := k.isLt; omega⟩

private lemma sequence_injective : Function.Injective (sequence (n := n)) := by
  intro r s equal
  apply Fin.ext
  have at_r := congrFun equal (⟨r.val, by have bound := r.isLt; omega⟩ : Rank n)
  have at_s := congrFun equal (⟨s.val, by have bound := s.isLt; omega⟩ : Rank n)
  simp only [sequence_eq_segment, segment_apply] at at_r at_s
  split_ifs at at_r at_s <;> omega

lemma nextLiveNonminimal_injective : Function.Injective (nextLiveNonminimal n) := by
  intro i j equal
  have same := sequence_injective (add_left_cancel equal)
  have indices := congrArg Fin.val same
  apply Fin.ext
  dsimp only at indices
  omega

noncomputable def nextLiveNonminimalEquiv (order : 2 ≤ n) :
    Fin (3 * n - 4) ≃
      {c : VirtualHand n // IsLiveFullWait 4 (n + 2) c ∧ ¬IsMinimalFullWait (n + 2) c} :=
  Equiv.ofBijective (fun k ↦ ⟨nextLiveNonminimal n k, by
    apply (next_live_not_minimal_iff order _).mpr
    refine ⟨⟨k.val + 1, by have bound := k.isLt; omega⟩, by dsimp; omega, ?_, rfl⟩
    have bound := k.isLt
    dsimp
    omega⟩) ⟨by
      intro i j equal
      exact nextLiveNonminimal_injective (congrArg Subtype.val equal), by
      rintro ⟨c, property⟩
      obtain ⟨r, lower, upper, equal⟩ := (next_live_not_minimal_iff order c).mp property
      let k : Fin (3 * n - 4) := ⟨r.val - 1, by omega⟩
      refine ⟨k, Subtype.ext ?_⟩
      have same : (⟨k.val + 1, by have bound := k.isLt; omega⟩ : Fin (3 * n - 2)) = r := by
        apply Fin.ext
        dsimp [k]
        omega
      change A n + sequence _ = c
      rw [same, ← equal]⟩

end Standard

lemma next_live_nonminimal_card (order : 2 ≤ n) :
    Nat.card {c : VirtualHand n // IsLiveFullWait 4 (n + 2) c ∧
      ¬IsMinimalFullWait (n + 2) c} = 3 * n - 4 :=
  Nat.card_eq_of_equiv_fin (Standard.nextLiveNonminimalEquiv order).symm

lemma taiwanese_live_nonminimal_card :
    Nat.card {c : VirtualHand 3 // IsLiveFullWait 4 5 c ∧ ¬IsMinimalFullWait 5 c} = 5 :=
  next_live_nonminimal_card (by decide +kernel)

namespace ClassBoundSharpness

lemma live (order : 2 ≤ n) : IsLiveFullWait 4 (n + 2) (hand n) := by
  apply isLiveFullWait_iff.mpr
  refine ⟨full order, ?_⟩
  intro i
  rw [hand_apply order]
  split_ifs <;> norm_num

lemma minimal (order : 2 ≤ n) : IsMinimalFullWait (n + 2) (hand n) := by
  apply (live order).minimal_next_of_missing_boundary order
  refine ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩
  rw [hand_apply order]
  simp

end ClassBoundSharpness

end Mahjong.VirtualHand
