/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Meldable.Scan

/-! The weighted-prefix closed form of the canonical scan. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

private def weightedPrefix (a : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range j, ((j - k : ℕ) : ℤ) * a k

private lemma weightedPrefix_succ (a : ℕ → ℤ) (j : ℕ) : weightedPrefix a (j + 1) =
    weightedPrefix a j + (∑ k ∈ Finset.range j, a k) + a j := by
  unfold weightedPrefix
  rw [Finset.sum_range_succ]
  have each : ∀ k ∈ Finset.range j, ((j + 1 - k : ℕ) : ℤ) * a k =
      ((j - k : ℕ) : ℤ) * a k + a k := by
    intro k inside
    have bound := Finset.mem_range.mp inside
    have shift : j + 1 - k = (j - k) + 1 := by omega
    rw [shift]
    push_cast
    ring
  rw [Finset.sum_congr rfl each]
  simp [Finset.sum_add_distrib]

private lemma weightedPrefix_second (a : ℕ → ℤ) (j : ℕ) :
    weightedPrefix a (j + 2) - 2 * weightedPrefix a (j + 1) + weightedPrefix a j = a (j + 1) := by
  have first := weightedPrefix_succ a j
  have second := weightedPrefix_succ a (j + 1)
  rw [Finset.sum_range_succ] at second
  rw [show j+1+1 = j+2 by omega] at second
  omega

private lemma weightedPrefix_cast_run (a : ℕ → ℤ) (j : ℕ) :
    ((weightedPrefix a j : ZMod 3), (weightedPrefix a (j - 1) : ZMod 3)) =
      SequenceScan.run (fun k ↦ (a k : ZMod 3)) j := by
  induction j with
  | zero => simp [weightedPrefix]
  | succ j ih =>
      rw [SequenceScan.run]
      simp only [← ih]
      cases j with
      | zero => simp [weightedPrefix]
      | succ k =>
          apply Prod.ext
          · change (weightedPrefix a (k + 2) : ZMod 3) = (a (k + 1) : ZMod 3) -
              (weightedPrefix a (k + 1) : ZMod 3) - (weightedPrefix a k : ZMod 3)
            have recurrence := congrArg (fun z : ℤ ↦ (z : ZMod 3)) (weightedPrefix_second a k)
            push_cast at recurrence
            have three : (3 : ZMod 3) * (weightedPrefix a (k + 1) : ZMod 3) = 0 := by
              rw [show (3 : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
            linear_combination recurrence + three
          · rfl

/-- `σ_j = (sum_(k=1)^j (j - k + 1)c_k) mod 3`, in zero-based vector indices. -/
lemma canonicalSequence_weighted (c : VirtualHand n) (j : ℕ) : canonicalSequence c j =
    (∑ k ∈ Finset.range j, ((j - k : ℕ) : ℤ) * coefficient c (k : ℤ)) % 3 := by
  let input := fun k : ℕ ↦ coefficient c (k : ℤ)
  have trace := (weightedPrefix_cast_run input j).trans
    (SequenceScan.run_map (Int.castAddHom (ZMod 3)) input j)
  have residue := (ZMod.intCast_eq_intCast_iff' _ _ 3).mp (congrArg Prod.fst trace).symm
  simpa [canonicalSequence, sequenceScan, weightedPrefix, input] using residue

end Mahjong.VirtualHand
