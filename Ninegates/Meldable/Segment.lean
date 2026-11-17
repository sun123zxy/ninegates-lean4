/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Hand.Segment
public import Ninegates.Meldable.Sequence

/-! An interval of single tiles is sequential whenever its length is a multiple
of three. The witness partitions the interval into consecutive sequences. -/

@[expose] public section

namespace Mahjong.VirtualHand

variable {n : ℕ}

lemma sequence_eq_segment (j : Fin (3 * n - 2)) :
    sequence j = segment j.val (j.val + 3) := by
  ext i
  simp only [sequence, Pi.add_apply, single_apply, Fin.ext_iff, segment_apply]
  split_ifs <;> omega

namespace Segment

def starts (a b k : ℤ) : ℤ :=
  if a ≤ k ∧ k + 3 ≤ b ∧ (k - a) % 3 = 0 then 1 else 0

lemma convolution (a b k : ℤ) (length : (b - a) % 3 = 0) :
    starts a b k + starts a b (k - 1) + starts a b (k - 2) =
      if a ≤ k ∧ k < b then 1 else 0 := by
  unfold starts
  split_ifs <;> omega

lemma coefficient_starts {a b : ℕ} (bound : b ≤ 3 * n) (k : ℤ) :
    coefficient (fun j : Fin (3 * n - 2) ↦ starts a b j.val) k = starts a b k := by
  by_cases inside : 0 ≤ k ∧ k < (3 * n - 2 : ℕ)
  · rw [coefficient, dite_eq_left inside]
    change starts a b (k.toNat : ℤ) = starts a b k
    congr 1
    omega
  · rw [coefficient, dite_eq_right inside]
    unfold starts
    split_ifs <;> omega

lemma sequenceHand_starts {a b : ℕ} (order : a ≤ b) (bound : b ≤ 3 * n)
    (length : (b - a) % 3 = 0) :
    sequenceHand (fun j : Fin (3 * n - 2) ↦ starts a b j.val) = segment a b := by
  have congruent : ((b : ℤ) - a) % 3 = 0 := by omega
  ext i
  simp only [sequenceHand_apply, coefficient_starts bound, segment_apply]
  have identity := convolution a b i.val congruent
  have inside : (a : ℤ) ≤ i.val ∧ (i.val : ℤ) < b ↔ a ≤ i.val ∧ i.val < b := by omega
  simpa only [inside] using identity

end Segment

lemma sequential_segment {a b : ℕ} (order : a ≤ b) (bound : b ≤ 3 * n)
    (length : (b - a) % 3 = 0) : Sequential (segment (n := n) a b) := by
  refine ⟨_, ?_, Segment.sequenceHand_starts order bound length⟩
  intro j
  dsimp only [Segment.starts]
  split_ifs <;> norm_num

lemma Sequential.add {c d : VirtualHand n} (hc : Sequential c) (hd : Sequential d) :
    Sequential (c + d) := by
  obtain ⟨s, positive_s, rfl⟩ := hc
  obtain ⟨t, positive_t, rfl⟩ := hd
  exact ⟨s + t, add_nonneg positive_s positive_t, map_add _ _ _⟩

lemma Sequential.smul {c : VirtualHand n} (h : Sequential c) {z : ℤ} (positive : 0 ≤ z) :
    Sequential (z • c) := by
  obtain ⟨s, coefficients, rfl⟩ := h
  refine ⟨z • s, ?_, map_smul _ _ _⟩
  intro j
  exact mul_nonneg positive (coefficients j)

lemma sequential_segment_sub_single {a b : ℕ} (bound : b ≤ 3 * n) (i : Rank n)
    (lower : a ≤ i.val) (upper : i.val < b) (left : (i.val - a) % 3 = 0)
    (right : (b - (i.val + 1)) % 3 = 0) : Sequential (segment a b - single i) := by
  rw [segment_split i lower upper]
  exact (sequential_segment lower (by omega) left).add
    (sequential_segment (by omega) bound right)

/-- Moving the first tile of an interval rightward by a multiple of three
splits it into two sequence intervals, with the moved tile at their overlap.
The target may equal the interval's right endpoint. -/
lemma sequential_segment_sub_first_add_single {a b : ℕ} (bound : b ≤ 3 * n)
    (i j : Rank n) (first : i.val = a) (lower : a ≤ j.val) (upper : j.val ≤ b)
    (left : (j.val - a) % 3 = 0) (right : (b - j.val) % 3 = 0) :
    Sequential (segment a b - single i + single j) := by
  have shape : segment a b - single i + single j =
      segment (a + 1) (j.val + 1) + segment j.val b := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, segment_apply, single_apply, Fin.ext_iff, first]
    split_ifs <;> omega
  rw [shape]
  exact (sequential_segment (by omega) (by omega) (by omega)).add
    (sequential_segment upper bound right)

end Mahjong.VirtualHand
