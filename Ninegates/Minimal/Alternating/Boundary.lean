/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Critical

/-! Critical draws in the short initial prefix of the alternating families. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

def prefixTripletDraw (b k : ℕ) : ℕ :=
  if b = 0 then if k = 2 then 3 else 4 else if k < 3 then 5 else 4

def prefixSequenceDraw (b r : ℕ) : ℕ :=
  if b = 0 then if r = 0 ∨ r = 3 then 5 else if r = 1 then 4 else 2
  else if r = 0 ∨ r = 3 then 4 else if r = 2 then 5 else 6

def prefixSequenceCover (b r : ℕ) : ℕ := if b = 0 ∧ r = 2 then 3 else r

lemma prefixSequenceCover_bounds (b r : ℕ) :
    r ≤ prefixSequenceCover b r ∧ prefixSequenceCover b r ≤ r + 1 := by
  unfold prefixSequenceCover
  split_ifs <;> omega

private lemma triplet_certificate (b : Fin 2) (k : Fin 5) (q : Fin 3)
    (lower : 1 ≤ k.val) (upper : k.val < 4 + b.val)
    (allowed : (prefixTripletDraw b.val k.val + q.val + b.val) % 3 = 2) :
    canonicalTriplet (PrefixModel.winning
      ⟨min (prefixTripletDraw b.val k.val) 5, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ q)
      (k.castLE (by decide : 5 ≤ 6)) = 0 := by
  have conditions := And.intro lower (And.intro upper allowed)
  fin_cases b <;> fin_cases k <;> fin_cases q
  all_goals norm_num [prefixTripletDraw] at conditions
  all_goals decide +kernel

private lemma sequence_certificate (b : Fin 2) (r : Fin 5) (q : Fin 3)
    (upper : r.val < 4 + b.val)
    (allowed : (prefixSequenceDraw b.val r.val + q.val + b.val) % 3 = 2) :
    canonicalSequence (PrefixModel.winning
      ⟨min (prefixSequenceDraw b.val r.val) 5, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ q)
      (r.val + 1) = 0 ∧
    canonicalTriplet (PrefixModel.winning
      ⟨min (prefixSequenceDraw b.val r.val) 5, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ q)
      ⟨prefixSequenceCover b.val r.val, by
        unfold prefixSequenceCover
        split_ifs <;> omega⟩ = 0 := by
  have conditions := And.intro upper allowed
  fin_cases b <;> fin_cases r <;> fin_cases q
  all_goals norm_num [prefixSequenceDraw] at conditions
  all_goals decide +kernel

lemma prefix_triplet_zero {n : ℕ} (order : 2 ≤ n) (i q k : Rank n)
    (lower : 1 ≤ k.val) (upper : k.val < 4 + n % 2)
    (draw : i.val = prefixTripletDraw (n % 2) k.val) (small : q.val < 3)
    (edge : DrawPair (hand n) i q) :
    canonicalTriplet (hand n + single i - pair q) k = 0 := by
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have certificate := triplet_certificate ⟨n % 2, by omega⟩ ⟨k.val, by omega⟩
    ⟨q.val, small⟩ lower upper (by simpa only [← draw] using congruent)
  rw [canonicalTriplet_eq_of_coefficient_prefix _ _ k
    (⟨k.val, by omega⟩ : Rank 2) rfl
    (PrefixModel.agree order i q small k.val (by omega) (by omega))]
  simpa only [draw, Fin.castLE_mk] using certificate

lemma prefix_sequence_obstruction {n : ℕ} (order : 2 ≤ n)
    (r : Fin (3 * n - 2)) (i q : Rank n) (upper : r.val < 4 + n % 2)
    (draw : i.val = prefixSequenceDraw (n % 2) r.val) (small : q.val < 3)
    (edge : DrawPair (hand n) i q) :
    canonicalSequence (hand n + single i - pair q) (r.val + 1) = 0 ∧
      ∃ k, sequence r k = 1 ∧ canonicalTriplet (hand n + single i - pair q) k = 0 := by
  have congruent := (draw_congruence_iff order i q).mp edge.congruence
  have certificate := sequence_certificate ⟨n % 2, by omega⟩ ⟨r.val, by omega⟩
    ⟨q.val, small⟩ upper (by simpa only [← draw] using congruent)
  have bounds := prefixSequenceCover_bounds (n % 2) r.val
  let k : Rank n := ⟨prefixSequenceCover (n % 2) r.val, by have := r.isLt; omega⟩
  have cover_bound : k.val ≤ 4 := by
    dsimp only [k]
    unfold prefixSequenceCover
    split_ifs <;> omega
  have cover_four : k.val = 4 → n % 2 = 1 := by
    dsimp only [k]
    unfold prefixSequenceCover
    split_ifs <;> omega
  constructor
  · rw [canonicalSequence_eq_of_coefficient_prefix _ _ (r.val + 1)
      (fun j before ↦ PrefixModel.agree order i q small r.val (by omega) (by omega) j
        (by omega))]
    simpa only [draw] using certificate.1
  · refine ⟨k, ?_, ?_⟩
    · simp only [sequence, Pi.add_apply, single_apply, Fin.ext_iff]
      dsimp only [k]
      unfold prefixSequenceCover
      split_ifs <;> omega
    · rw [canonicalTriplet_eq_of_coefficient_prefix _ _ k
        (⟨k.val, by omega⟩ : Rank 2) rfl
        (PrefixModel.agree order i q small k.val cover_bound cover_four)]
      simpa only [draw, k] using certificate.2

end Mahjong.VirtualHand.AlternatingWait
