/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Standard.Distinct
public import Ninegates.Classification
public import Ninegates.Minimal.One
public import Mathlib.SetTheory.Cardinal.Finite

/-! Exact cardinalities obtained from the structural classifications. -/

@[expose] public section

namespace Mahjong.VirtualHand

noncomputable def Standard.eightFullWaitEquiv {n : ℕ} (order : 2 ≤ n) :
    Fin 8 ≃ {c : VirtualHand n // IsFullWait (n + 1) c} :=
  Equiv.ofBijective (fun k ↦ ⟨Standard.Eight n k,
    ((Standard.eightFamily_iff_exists _).mpr ⟨k, rfl⟩).full order⟩) ⟨by
      intro i j equal
      exact Standard.Eight_injective order (congrArg Subtype.val equal), by
      rintro ⟨c, full⟩
      obtain ⟨k, equal⟩ := (Standard.eightFamily_iff_exists c).mp (full.eightFamily order)
      exact ⟨k, Subtype.ext equal.symm⟩⟩

noncomputable def Standard.oneFullWaitEquiv :
    Fin 6 ≃ {c : VirtualHand 1 // IsFullWait 2 c} :=
  Equiv.ofBijective (fun k ↦ ⟨Standard.One k, (Standard.One_live k).1⟩) ⟨by
    intro i j equal
    exact Standard.One_injective (congrArg Subtype.val equal), by
    rintro ⟨c, full⟩
    obtain ⟨k, equal⟩ := full.orderOneFamily
    exact ⟨k, Subtype.ext equal.symm⟩⟩

lemma fullWait_card_eight {n : ℕ} (order : 2 ≤ n) :
    Nat.card {c : VirtualHand n // IsFullWait (n + 1) c} = 8 :=
  Nat.card_eq_of_equiv_fin (Standard.eightFullWaitEquiv order).symm

lemma fullWait_card_six : Nat.card {c : VirtualHand 1 // IsFullWait 2 c} = 6 :=
  Nat.card_eq_of_equiv_fin Standard.oneFullWaitEquiv.symm

lemma minimalFullWait_card_eight {n : ℕ} (order : 2 ≤ n) :
    Nat.card {c : VirtualHand n // IsMinimalFullWait (n + 1) c} = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ ↦ isMinimalFullWait_succ_iff))]
  exact fullWait_card_eight order

lemma minimalFullWait_card_six : Nat.card {c : VirtualHand 1 // IsMinimalFullWait 2 c} = 6 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ ↦ isMinimalFullWait_succ_iff))]
  exact fullWait_card_six

lemma orderOne_minimalFullWait_card (m : ℕ) :
    Nat.card {c : VirtualHand 1 // IsMinimalFullWait m c} = if m = 2 then 6 else 0 := by
  by_cases two : m = 2
  · subst m
    simpa using minimalFullWait_card_six
  · let : IsEmpty {c : VirtualHand 1 // IsMinimalFullWait m c} := ⟨fun c ↦
      two (orderOne_isMinimalFullWait_iff.mp c.property).1⟩
    simp [two]

lemma liveFullWait_card_one {n : ℕ} (order : 2 ≤ n) :
    Nat.card {c : VirtualHand n // IsLiveFullWait 4 (n + 1) c} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨Standard.A n, Standard.A_live order⟩, ?_⟩
  intro c
  exact Subtype.ext (liveFullWait_unique order c.property)

lemma orderOne_liveFullWait_card : Nat.card {c : VirtualHand 1 // IsLiveFullWait 4 2 c} = 6 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun _ ↦ orderOne_isLiveFullWait_iff_isOrderOneFamily.trans
      orderOne_isFullWait_iff_isOrderOneFamily.symm))]
  exact fullWait_card_six

lemma fullWait_card_zero {n m : ℕ} (bound : m ≤ n) :
    Nat.card {c : VirtualHand n // IsFullWait m c} = 0 := by
  let : IsEmpty {c : VirtualHand n // IsFullWait m c} := ⟨fun c ↦ by
    have lower := c.property.meldCount_gt_order
    omega⟩
  exact Nat.card_of_isEmpty

lemma minimalFullWait_card_zero {n m : ℕ} (bound : m ≤ n) :
    Nat.card {c : VirtualHand n // IsMinimalFullWait m c} = 0 := by
  let : IsEmpty {c : VirtualHand n // IsMinimalFullWait m c} := ⟨fun c ↦ by
    have lower := c.property.meldCount_gt_order
    omega⟩
  exact Nat.card_of_isEmpty

lemma orderOne_allMinimalFullWait_card :
    Nat.card {c : VirtualHand 1 // ∃ m, IsMinimalFullWait m c} = 6 := by
  have same (c : VirtualHand 1) : (∃ m, IsMinimalFullWait m c) ↔ IsFullWait 2 c := by
    constructor
    · rintro ⟨m, minimal⟩
      obtain ⟨rfl, family⟩ := orderOne_isMinimalFullWait_iff.mp minimal
      exact orderOne_isFullWait_iff_isOrderOneFamily.mpr family
    · intro full
      exact ⟨2, full.minimal_succ⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight same)]
  exact fullWait_card_six

end Mahjong.VirtualHand
