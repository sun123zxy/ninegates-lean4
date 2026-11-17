/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import ComparatorChallenges.Bridges

/-! Numbered-result correspondence for the PUBLIC paper:
Shubin Xue and Xingyu Zhong, arXiv:2611.06944v1, submitted 2026-11-02.
PDF: https://arxiv.org/pdf/2611.06944v1
HTML: https://arxiv.org/html/2611.06944v1
PDF SHA-256:
174b9a8be2f5c01fe31550a7d4695e35d70047597b328064abaaa86b49eb8b50

Entries follow the published order, including definitions and open questions.
The full source metadata and explicit coverage status are in `paper.json`.
Lean rank indices are zero-based; `rank i = i.val+1` is the paper's rank.
The independent derived-object definitions are in `Model.lean`.
Only completed proofs appear as declarations below. The configuration lists
those declarations explicitly; deferred/open entries are marked in place. -/

@[expose] public section

namespace ComparatorChallenges

open Mahjong Mahjong.VirtualHand

/-! Paper Theorem 1.1
Theorem 1.1 (Classification of full-sided waits).
https://arxiv.org/html/2611.06944v1#S1.Thmcounter1 -/

theorem theorem_1_1_orderOne_isFullWait_iff_isOrderOneFamily :
    ∀ {c : VirtualHand 1}, IsFullWait 2 c ↔ Spec.Standard.OrderOneFamily c := by
  exact @Mahjong.VirtualHand.orderOne_isFullWait_iff_isOrderOneFamily

theorem theorem_1_1_orderOne_isLiveFullWait_iff_isOrderOneFamily :
    ∀ {c : VirtualHand 1}, IsLiveFullWait 4 2 c ↔ Spec.Standard.OrderOneFamily c := by
  exact @Mahjong.VirtualHand.orderOne_isLiveFullWait_iff_isOrderOneFamily

theorem theorem_1_1_fullWait_card_six :
    Nat.card { c : VirtualHand 1 // IsFullWait 2 c } = 6 := by
  exact @Mahjong.VirtualHand.fullWait_card_six

theorem theorem_1_1_isFullWait_iff_eightFamily :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → (IsFullWait (n + 1) c ↔
    Spec.Standard.EightFamily c) := by
  exact @Mahjong.VirtualHand.isFullWait_iff_eightFamily

theorem theorem_1_1_fullWait_card_eight :
    ∀ {n : ℕ}, 2 ≤ n → Nat.card { c : VirtualHand n // IsFullWait (n + 1) c } = 8 := by
  exact @Mahjong.VirtualHand.fullWait_card_eight

theorem theorem_1_1_isLiveFullWait_iff_eq_A :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → (IsLiveFullWait 4 (n + 1) c ↔ c =
    Spec.Standard.A n) := by
  exact @Mahjong.VirtualHand.isLiveFullWait_iff_eq_A

theorem theorem_1_1_reverse_A :
    ∀ n : ℕ, reverse (Spec.Standard.A n) = Spec.Standard.A n := by
  exact @Mahjong.VirtualHand.Standard.reverse_A

theorem theorem_1_1_reverse_E :
    ∀ {n : ℕ}, 2 ≤ n → reverse (Spec.Standard.E n) = Spec.Standard.E n := by
  exact @Mahjong.VirtualHand.Standard.reverse_E

theorem theorem_1_1_valid_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, IsFullWait (n + 1) c → Valid c := by
  exact @Mahjong.VirtualHand.IsFullWait.valid_succ

/-! Paper Proposition 2.1
https://arxiv.org/html/2611.06944v1#S2.Thmcounter1 -/

theorem proposition_2_1_size_eq_classSizes :
    ∀ {n : ℕ} (c : VirtualHand n), size c = classSize 0 c + classSize 1 c + classSize 2 c := by
  exact @Mahjong.VirtualHand.size_eq_classSizes

theorem proposition_2_1_rankSum_cast_eq_classSizes :
    ∀ {n : ℕ} (c : VirtualHand n), (rankSum c : ZMod 3) = (classSize 1 c : ZMod 3) + 2 *
      (classSize 2 c : ZMod 3) := by
  exact @Mahjong.VirtualHand.rankSum_cast_eq_classSizes

theorem proposition_2_1_classSizes_congruent_iff :
    ∀ {n : ℕ} (c : VirtualHand n), (classSize 0 c : ZMod 3) = (classSize 1 c : ZMod 3) ∧
      (classSize 1 c : ZMod 3) = (classSize 2 c : ZMod 3) ↔ (size c : ZMod 3) = 0 ∧
      (rankSum c : ZMod 3) = 0 := by
  exact @Mahjong.VirtualHand.classSizes_congruent_iff

theorem proposition_2_1_rank_sum_difference :
    ∀ {n : ℕ} (c : VirtualHand n), (rankSum c : ZMod 3) = (classSize 1 c : ZMod 3) -
    (classSize 2 c : ZMod 3) := by
  intro n c
  have sum := rankSum_cast_eq_classSizes c
  have three : (3 : ZMod 3) = 0 := by decide +kernel
  have zero : (3 : ZMod 3) * (classSize 2 c : ZMod 3) = 0 := by rw [three, zero_mul]
  linear_combination sum + zero

/-! Paper Definition 2.2
https://arxiv.org/html/2611.06944v1#S2.Thmcounter2 -/

-- Model: IsFullWait, IsLiveFullWait.

theorem definition_2_2_isFullWait_iff :
    ∀ {n m : ℕ} {c : VirtualHand n}, IsFullWait m c ↔
      Nonnegative c ∧ size c = 3 * (m : ℤ) + 1 ∧ ∀ i : Rank n, ∃ j, DrawPair c i j := by
  exact @Mahjong.VirtualHand.isFullWait_iff

theorem definition_2_2_isLiveFullWait_iff :
    ∀ {n m cap : ℕ} {c : VirtualHand n}, IsLiveFullWait cap m c ↔
      IsFullWait m c ∧ ∀ i : Rank n, c i + 1 ≤ (cap : ℤ) := by
  exact @Mahjong.VirtualHand.isLiveFullWait_iff

/-! Paper Definition 3.1
Definition 3.1 (Meld placement).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter1 -/

-- Model: Placement, Placement.Nonnegative, Placement.toHand; Spec.sequenceHand, Spec.Sequential.

theorem definition_3_1_toHand_apply :
    ∀ {n : ℕ} (p : Placement n) (i : Rank n),
      p.toHand i = Spec.coefficient p.seqNum (i.val : ℤ) +
        Spec.coefficient p.seqNum ((i.val : ℤ) - 1) +
        Spec.coefficient p.seqNum ((i.val : ℤ) - 2) + 3 * p.tripNum i := by
  exact @Mahjong.VirtualHand.Placement.toHand_apply

theorem definition_3_1_sequenceHand_apply :
    ∀ {n : ℕ} (s : Fin (3 * n - 2) → ℤ) (i : Rank n),
      Spec.sequenceHand (n := n) s i = Spec.coefficient s (i.val : ℤ) +
        Spec.coefficient s ((i.val : ℤ) - 1) + Spec.coefficient s ((i.val : ℤ) - 2) := by
  exact @Mahjong.VirtualHand.sequenceHand_apply

/-! Paper Proposition 3.2
Proposition 3.2 (Characterization of virtual sequence placements).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter2 -/

theorem proposition_3_2_sequenceScan_closed_form :
    ∀ {n : ℕ} (c : VirtualHand n) (j : ℕ),
      (Spec.sequenceScan c j).1 = ∑ t ∈ Finset.range ((j + 2) / 3),
        (Spec.coefficient c ((j : ℤ) - 1 - 3 * (t : ℤ)) -
          Spec.coefficient c ((j : ℤ) - 2 - 3 * (t : ℤ))) := by
  simpa only [Bridges.sequenceScan_eq, Bridges.coefficient_eq] using
    (@Mahjong.VirtualHand.sequenceScan_closed_form)

theorem proposition_3_2_sequenceScan_boundary :
    ∀ {n : ℕ} (c : VirtualHand n), Spec.sequenceScan c (3 * n) =
      (classSize 0 c - classSize 2 c, classSize 2 c - classSize 1 c) := by
  simpa only [Bridges.sequenceScan_eq] using
    (@Mahjong.VirtualHand.sequenceScan_boundary)

theorem proposition_3_2_sequenceHand_injective :
    ∀ {n : ℕ}, Function.Injective (Spec.sequenceHand (n := n)) := by
  exact @Mahjong.VirtualHand.sequenceHand_injective

theorem proposition_3_2_virtuallySequential_iff_classSizes :
    ∀ {n : ℕ} (c : VirtualHand n), Spec.VirtuallySequential c ↔ classSize 0 c = classSize 1 c ∧
      classSize 1 c = classSize 2 c := by
  exact @Mahjong.VirtualHand.virtuallySequential_iff_classSizes

theorem proposition_3_2_sequential_iff_classSizes :
    ∀ {n : ℕ} (c : VirtualHand n), Spec.Sequential c ↔ (classSize 0 c = classSize 1 c ∧
      classSize 1 c = classSize 2 c) ∧ 0 ≤ Spec.recoveredSequences c := by
  simpa only [Bridges.recoveredSequences_eq, Bridges.sequential_iff] using
    (@Mahjong.VirtualHand.sequential_iff_classSizes)

theorem proposition_3_2_unique :
    ∀ {n : ℕ} {c : VirtualHand n},
      Spec.VirtuallySequential c → ∃! s, Spec.sequenceHand (n := n) s = c := by
  exact @Mahjong.VirtualHand.VirtuallySequential.unique

theorem proposition_3_2_recurrence_uniqueness :
    ∀ {n : ℕ} (c : VirtualHand n) (s : ℕ → ℤ), s 0 = 0 → (∀ k < 3 * n, s (k + 1) =
    Spec.coefficient c (k : ℤ) - s k - s (k - 1)) → ∀ k ≤ 3 * n, s k = (Spec.sequenceScan
    c k).1 := by
  intro n c s initial recurrence k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro bound
    cases k with
    | zero => exact initial
    | succ k =>
      have previous := ih k (by omega) (by omega)
      have older : s (k - 1) = (Spec.sequenceScan c k).2 := by
        cases k with
        | zero => exact initial
        | succ j =>
          have old := ih j (by omega) (by omega)
          simpa only [Nat.add_sub_cancel, Spec.sequenceScan, Spec.SequenceScan.run] using old
      rw [recurrence k (by omega), previous, older]
      rfl

/-! Paper Definition 3.3
Definition 3.3 (Canonicity).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter3 -/

-- Model: Spec.Placement.Canonic.

/-! Paper Proposition 3.4
Proposition 3.4 (Canonicalization).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter4 -/

theorem proposition_3_4_canonic_canonicalize :
    ∀ {n : ℕ} (p : Placement n), Spec.Placement.Canonic (Spec.Placement.canonicalize p) := by
  exact @Mahjong.VirtualHand.Placement.canonic_canonicalize

theorem proposition_3_4_toHand_canonicalize :
    ∀ {n : ℕ} (p : Placement n), (Spec.Placement.canonicalize p).toHand = p.toHand := by
  exact @Mahjong.VirtualHand.Placement.toHand_canonicalize

theorem proposition_3_4_nonnegative_canonicalize :
    ∀ {n : ℕ} {p : Placement n}, Placement.Nonnegative p → Placement.Nonnegative
    (Spec.Placement.canonicalize p) := by
  exact @Mahjong.VirtualHand.Placement.nonnegative_canonicalize

/-! Paper Definition 3.5
Definition 3.5 (Triplet-greedy scan).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter5 -/

-- Model: Spec.canonicalSequence, Spec.canonicalTriplet, Spec.scanPlacement.

theorem definition_3_5_canonicalSequence_zero :
    ∀ {n : ℕ} (c : VirtualHand n), Spec.canonicalSequence c 0 = 0 := by
  simpa only [Bridges.canonicalSequence_eq] using
    (@Mahjong.VirtualHand.canonicalSequence_zero)

theorem definition_3_5_canonicalSequence_succ :
    ∀ {n : ℕ} (c : VirtualHand n) (k : ℕ),
      Spec.canonicalSequence c (k + 1) =
        (Spec.coefficient c (k : ℤ) - Spec.canonicalSequence c k -
          Spec.canonicalSequence c (k - 1)) % 3 := by
  simpa only [Bridges.canonicalSequence_eq, Bridges.coefficient_eq] using
    (@Mahjong.VirtualHand.canonicalSequence_succ)

theorem definition_3_5_canonicalTriplet_eq :
    ∀ {n : ℕ} (c : VirtualHand n) (i : Rank n),
      Spec.canonicalTriplet c i =
        (c i - Spec.canonicalSequence c i.val - Spec.canonicalSequence c (i.val - 1)) / 3 := by
  simpa only [Bridges.canonicalSequence_eq, Bridges.canonicalTriplet_eq] using
    (@Mahjong.VirtualHand.canonicalTriplet_eq)

theorem definition_3_5_canonicalSequence_bounds :
    ∀ {n : ℕ} (c : VirtualHand n) (j : ℕ), 0 ≤ Spec.canonicalSequence c j ∧
    Spec.canonicalSequence c j < 3 := by
  simpa only [Bridges.canonicalSequence_eq] using
    (@Mahjong.VirtualHand.canonicalSequence_bounds)

/-! Paper Proposition 3.6
Proposition 3.6 (Criterion of (virtual) meldability).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter6 -/

theorem proposition_3_6_canonicalSequence_weighted :
    ∀ {n : ℕ} (c : VirtualHand n) (j : ℕ),
      Spec.canonicalSequence c j =
        (∑ k ∈ Finset.range j, ((j - k : ℕ) : ℤ) * Spec.coefficient c (k : ℤ)) % 3 := by
  simpa only [Bridges.canonicalSequence_eq, Bridges.coefficient_eq] using
    (@Mahjong.VirtualHand.canonicalSequence_weighted)

theorem proposition_3_6_canonicalSequence_boundary :
    ∀ {n : ℕ} (c : VirtualHand n),
      (Spec.canonicalSequence c (3 * n), Spec.canonicalSequence c (3 * n - 1)) =
        ((classSize 0 c - classSize 2 c) % 3, (classSize 2 c - classSize 1 c) % 3) := by
  simpa only [Bridges.canonicalSequence_eq] using
    (@Mahjong.VirtualHand.canonicalSequence_boundary)

theorem proposition_3_6_exists_unique_canonical_iff :
    ∀ {n : ℕ} (c : VirtualHand n), (∃! p, Spec.Placement.Canonic p ∧ p.toHand = c) ↔
      (size c : ZMod 3) = 0 ∧ (rankSum c : ZMod 3) = 0 := by
  exact @Mahjong.VirtualHand.exists_unique_canonical_iff

theorem proposition_3_6_virtuallyMeldable_iff_canonicalSequence :
    ∀ {n : ℕ} (c : VirtualHand n), VirtuallyMeldable c ↔ Spec.canonicalSequence c (3 * n)
    = 0 ∧ Spec.canonicalSequence c (3 * n - 1) = 0 := by
  simpa only [Bridges.canonicalSequence_eq] using
    (@Mahjong.VirtualHand.virtuallyMeldable_iff_canonicalSequence)

theorem proposition_3_6_virtuallyMeldable_iff_classSizes :
    ∀ {n : ℕ} (c : VirtualHand n), VirtuallyMeldable c ↔ (classSize 0 c : ZMod 3) =
      (classSize 1 c : ZMod 3) ∧ (classSize 1 c : ZMod 3) = (classSize 2 c : ZMod 3) := by
  exact @Mahjong.VirtualHand.virtuallyMeldable_iff_classSizes

theorem proposition_3_6_virtuallyMeldable_iff_size_rankSum :
    ∀ {n : ℕ} (c : VirtualHand n), VirtuallyMeldable c ↔ (size c : ZMod 3) = 0 ∧
      (rankSum c : ZMod 3) = 0 := by
  exact @Mahjong.VirtualHand.virtuallyMeldable_iff_size_rankSum

theorem proposition_3_6_meldable_iff_tripletGreedy :
    ∀ {n : ℕ} (c : VirtualHand n), Meldable c ↔
      (Spec.canonicalSequence c (3 * n) = 0 ∧ Spec.canonicalSequence c (3 * n - 1) = 0) ∧
        ∀ i : Rank n, 0 ≤ Spec.canonicalTriplet c i := by
  simpa only [Bridges.canonicalSequence_eq, Bridges.canonicalTriplet_eq] using
    (@Mahjong.VirtualHand.meldable_iff_tripletGreedy)

theorem proposition_3_6_scanPlacement_canonic :
    ∀ {n : ℕ} (c : VirtualHand n), Spec.Placement.Canonic (Spec.scanPlacement c) := by
  simpa only [Bridges.scanPlacement_eq, Bridges.canonic_iff] using
    (@Mahjong.VirtualHand.scanPlacement_canonic)

theorem proposition_3_6_scanPlacement_toHand :
    ∀ {n : ℕ} {c : VirtualHand n},
      VirtuallyMeldable c → (Spec.scanPlacement c).toHand = c := by
  simpa only [Bridges.scanPlacement_eq] using
    (@Mahjong.VirtualHand.scanPlacement_toHand)

theorem proposition_3_6_scanPlacement_eq :
    ∀ {n : ℕ} {p : Placement n},
      Spec.Placement.Canonic p → Spec.scanPlacement p.toHand = p := by
  simpa only [Bridges.scanPlacement_eq, Bridges.canonic_iff] using
    (@Mahjong.VirtualHand.Placement.Canonic.scanPlacement_eq)

theorem proposition_3_6_VirtuallyMeldable_unique_canonical :
    ∀ {n : ℕ} {c : VirtualHand n}, VirtuallyMeldable c → ∃! p, Spec.Placement.Canonic p ∧
    p.toHand = c := by
  exact @Mahjong.VirtualHand.VirtuallyMeldable.unique_canonical

theorem proposition_3_6_Meldable_unique_canonical :
    ∀ {n : ℕ} {c : VirtualHand n}, Meldable c → ∃! p, Placement.Nonnegative p ∧
    Spec.Placement.Canonic p ∧ p.toHand = c := by
  exact @Mahjong.VirtualHand.Meldable.unique_canonical

/-! Paper Proposition 3.7
https://arxiv.org/html/2611.06944v1#S3.Thmcounter7 -/

theorem proposition_3_7_canonicalSequence_prefix_iff :
    ∀ {n : ℕ} (c d : VirtualHand n), ∀ k ≤ 3 * n,
      (∀ i : Rank n, i.val < k → (c i : ZMod 3) = (d i : ZMod 3)) ↔
        ∀ j ≤ k, Spec.canonicalSequence c j = Spec.canonicalSequence d j := by
  simpa only [Bridges.canonicalSequence_eq] using
    (@Mahjong.VirtualHand.canonicalSequence_prefix_iff)

/-! Paper Proposition 3.8
Proposition 3.8 (Sequential tile moving).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter8 -/

theorem proposition_3_8_sequential_moveTile_right_iff :
    ∀ {n : ℕ} {s : Fin (3 * n - 2) → ℤ}, 0 ≤ s →
      ∀ i j : Rank n, i.val ≤ j.val →
        (Spec.Sequential (Spec.moveTile (Spec.sequenceHand (n := n) s) i j) ↔
          rankClass i = rankClass j ∧
            ∀ r : Fin (3 * n - 2), i.val ≤ r.val → r.val < j.val →
              (r.val - i.val) % 3 = 0 → 1 ≤ s r) := by
  exact @Mahjong.VirtualHand.sequential_moveTile_right_iff

theorem proposition_3_8_sequential_moveTile_left_iff :
    ∀ {n : ℕ} {s : Fin (3 * n - 2) → ℤ}, 0 ≤ s →
      ∀ i j : Rank n, j.val ≤ i.val →
        (Spec.Sequential (Spec.moveTile (Spec.sequenceHand (n := n) s) i j) ↔
          rankClass i = rankClass j ∧
            ∀ r : Fin (3 * n - 2), j.val ≤ r.val → r.val < i.val →
              (r.val - j.val) % 3 = 1 → 1 ≤ s r) := by
  exact @Mahjong.VirtualHand.sequential_moveTile_left_iff

theorem proposition_3_8_sequenceHand_shiftAlong :
    ∀ {n : ℕ} (s : Fin (3 * n - 2) → ℤ) (i j : Rank n),
      i.val ≤ j.val → rankClass i = rankClass j →
        Spec.sequenceHand (n := n) (Spec.Moving.shiftAlong s i j) =
          Spec.moveTile (Spec.sequenceHand (n := n) s) i j := by
  exact @Mahjong.VirtualHand.Moving.sequenceHand_shiftAlong

theorem proposition_3_8_sequenceHand_shiftAlongLeft :
    ∀ {n : ℕ} (s : Fin (3 * n - 2) → ℤ) (i j : Rank n),
      j.val ≤ i.val → rankClass i = rankClass j →
        Spec.sequenceHand (n := n) (Spec.Moving.shiftAlongLeft s i j) =
          Spec.moveTile (Spec.sequenceHand (n := n) s) i j := by
  exact @Mahjong.VirtualHand.Moving.sequenceHand_shiftAlongLeft

/-! Paper Proposition 3.9
Proposition 3.9 (Tile moving).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter9 -/

theorem proposition_3_9_meldable_right_iff :
    ∀ {n : ℕ} {p : Placement n}, Spec.Placement.Canonic p → Placement.Nonnegative p →
      ∀ r : Spec.Moving.Start n, Meldable (Spec.Moving.right p.toHand r) ↔
        1 ≤ p.seqNum (Spec.Moving.sequenceAt r 0) ∧
          p.seqNum (Spec.Moving.sequenceAt r 1) ≤ 1 ∨
        1 ≤ p.seqNum (Spec.Moving.sequenceAt r 0) ∧
          p.seqNum (Spec.Moving.sequenceAt r 1) = 2 ∨
        p.seqNum (Spec.Moving.sequenceAt r 0) = 0 ∧
          p.seqNum (Spec.Moving.sequenceAt r 1) ≤ 1 ∧
          1 ≤ p.tripNum (Spec.Moving.rankAt r 0) ∧
          1 ≤ p.tripNum (Spec.Moving.rankAt r 1) ∧
          1 ≤ p.tripNum (Spec.Moving.rankAt r 2) ∨
        p.seqNum (Spec.Moving.sequenceAt r 0) = 0 ∧
          p.seqNum (Spec.Moving.sequenceAt r 1) = 2 ∧
          1 ≤ p.tripNum (Spec.Moving.rankAt r 0) := by
  exact @Mahjong.VirtualHand.Moving.meldable_right_iff

theorem proposition_3_9_canonical_step_seqNum :
    ∀ {n : ℕ} {p : Placement n}, Spec.Placement.Canonic p → ∀ r : Spec.Moving.Start n,
      (Spec.Placement.canonicalize (Spec.Moving.step p r)).seqNum =
        Spec.Moving.shift p.seqNum r +
          (3 * Spec.Moving.borrow p r) • Pi.single (Spec.Moving.sequenceAt r 0) 1 -
          (3 * Spec.Moving.carry p r) • Pi.single (Spec.Moving.sequenceAt r 1) 1 := by
  exact @Mahjong.VirtualHand.Moving.canonical_step_seqNum

theorem proposition_3_9_canonical_step_tripNum :
    ∀ {n : ℕ} {p : Placement n}, Spec.Placement.Canonic p → ∀ r : Spec.Moving.Start n,
      (Spec.Placement.canonicalize (Spec.Moving.step p r)).tripNum =
        p.tripNum - Spec.Moving.borrow p r • sequence (Spec.Moving.sequenceAt r 0) +
          Spec.Moving.carry p r • sequence (Spec.Moving.sequenceAt r 1) := by
  exact @Mahjong.VirtualHand.Moving.canonical_step_tripNum

theorem proposition_3_9_meldable_right_of_long :
    ∀ {n : ℕ} {c : VirtualHand n}, Meldable c →
      ∀ (r : Spec.Moving.Start n) (j : Rank n), r.val + 3 ≤ j.val →
        Meldable (Spec.moveTile c (Spec.Moving.rankAt r 0) j) →
          Meldable (Spec.Moving.right c r) := by
  exact @Mahjong.VirtualHand.Moving.meldable_right_of_long

theorem proposition_3_9_moveTile_right_steps :
    ∀ {n : ℕ} {c : VirtualHand n}, Meldable c →
      ∀ (i j k : Rank n) (t : ℕ), k.val = i.val + 3 * t → k.val ≤ j.val →
        Meldable (Spec.moveTile c i j) → Meldable (Spec.moveTile c i k) := by
  exact @Mahjong.VirtualHand.Meldable.moveTile_right_steps

/-! Paper Proposition 3.10
Proposition 3.10 (Interval property of tile moving).
https://arxiv.org/html/2611.06944v1#S3.Thmcounter10 -/

theorem proposition_3_10_moveTile_interval :
    ∀ {n : ℕ} {c : VirtualHand n}, Meldable c →
      ∀ {i j k : Rank n}, Meldable (Spec.moveTile c i j) →
        min i.val j.val ≤ k.val ∧ k.val ≤ max i.val j.val →
          rankClass k = rankClass i → Meldable (Spec.moveTile c i k) := by
  exact @Mahjong.VirtualHand.Meldable.moveTile_interval

theorem proposition_3_10_moveTile_interval_of_endpoints :
    ∀ {n : ℕ} {c : VirtualHand n} {i a b k : Rank n},
      Meldable (Spec.moveTile c i a) → Meldable (Spec.moveTile c i b) →
        min a.val b.val ≤ k.val ∧ k.val ≤ max a.val b.val →
          rankClass k = rankClass a → Meldable (Spec.moveTile c i k) := by
  exact @Mahjong.VirtualHand.moveTile_interval_of_endpoints

/-! Paper Definition 4.1
Definition 4.1 (Draw-pair relation).
https://arxiv.org/html/2611.06944v1#S4.Thmcounter1 -/

-- Model: DrawPair.

/-! Paper Proposition 4.2
https://arxiv.org/html/2611.06944v1#S4.Thmcounter2 -/

theorem proposition_4_2_congruence :
    ∀ {n : ℕ} {c : VirtualHand n} {i j : Rank n},
      DrawPair c i j → rankClass i + rankClass j = -(rankSum c : ZMod 3) := by
  exact @Mahjong.VirtualHand.DrawPair.congruence

/-! Paper Definition 4.3
https://arxiv.org/html/2611.06944v1#S4.Thmcounter3 -/

-- Model: Spec.fixedClass, Spec.pairedClass.

theorem definition_4_3_pairedClass_pairedClass :
    ∀ {n : ℕ} (c : VirtualHand n) (r : ZMod 3), Spec.pairedClass c (Spec.pairedClass c r)
    = r := by
  exact @Mahjong.VirtualHand.pairedClass_pairedClass

theorem definition_4_3_pairedClass_eq_self_iff :
    ∀ {n : ℕ} (c : VirtualHand n) (r : ZMod 3), Spec.pairedClass c r = r ↔ r =
    Spec.fixedClass c := by
  exact @Mahjong.VirtualHand.pairedClass_eq_self_iff

theorem definition_4_3_pairedClass_eq_fixed_iff :
    ∀ {n : ℕ} (c : VirtualHand n) (r : ZMod 3), Spec.pairedClass c r = Spec.fixedClass c ↔
    r = Spec.fixedClass c := by
  exact @Mahjong.VirtualHand.pairedClass_eq_fixed_iff

/-! Paper Proposition 4.4
https://arxiv.org/html/2611.06944v1#S4.Thmcounter4 -/

theorem proposition_4_4_classSize_nonfixed_congruence :
    ∀ {n : ℕ} {c : VirtualHand n}, (size c : ZMod 3) = 1 →
      ∀ r : ZMod 3, r ≠ Spec.fixedClass c →
        (classSize r c : ZMod 3) + 1 = (classSize (Spec.fixedClass c) c : ZMod 3) := by
  exact @Mahjong.VirtualHand.classSize_nonfixed_congruence

/-! Paper Example 4.5
Example 4.5 (Draw-pair relation of $\mathbf{A}_{n}$ ).
https://arxiv.org/html/2611.06944v1#S4.Thmcounter5 -/

theorem example_4_5 :
    ∀ {n : ℕ}, 0 < n → Spec.fixedClass (Spec.Standard.A n) = 2 ∧ ∀ i j : Rank n, DrawPair
    (Spec.Standard.A n) i j ↔ (rankClass i = 0 ∧ j.val = 0) ∨ (rankClass i = 1 ∧ j.val + 1
    = 3 * n) ∨ (rankClass i = 2 ∧ j = i) := by
  intro n positive
  exact ⟨Standard.fixedClass_A positive, fun i j ↦ Standard.A_drawPair_iff positive i j⟩

/-! Paper Proposition 4.6
Proposition 4.6 (Incoming interval property).
https://arxiv.org/html/2611.06944v1#S4.Thmcounter6 -/

theorem proposition_4_6_incoming_interval :
    ∀ {n : ℕ} {c : VirtualHand n} {i p q : Rank n},
      DrawPair c p q → DrawPair c i q → ∀ k : Rank n,
        min p.val i.val ≤ k.val ∧ k.val ≤ max p.val i.val →
          rankClass k = rankClass p → DrawPair c k q := by
  exact @Mahjong.VirtualHand.DrawPair.incoming_interval

theorem proposition_4_6_same_draw_class :
    ∀ {n : ℕ} {c : VirtualHand n} {i p q : Rank n}, DrawPair c p q → DrawPair c i q →
    rankClass p = rankClass i := by
  exact @Mahjong.VirtualHand.DrawPair.same_draw_class

/-! Paper Definition 4.7
Definition 4.7 (Two-pair decomposition).
https://arxiv.org/html/2611.06944v1#S4.Thmcounter7 -/

-- Model: Spec.TwoPair.

/-! Paper Proposition 4.8
Proposition 4.8 (Bidirectional edges and two-pair decompositions).
https://arxiv.org/html/2611.06944v1#S4.Thmcounter8 -/

theorem proposition_4_8_bidirectional_iff_twoPair :
    ∀ {n : ℕ} {c : VirtualHand n} {p q : Rank n}, p ≠ q → (DrawPair c p q ∧ DrawPair c q p
    ↔ Spec.TwoPair c p q) := by
  exact @Mahjong.VirtualHand.bidirectional_iff_twoPair

/-! Paper Proposition 4.9
https://arxiv.org/html/2611.06944v1#S4.Thmcounter9 -/

theorem proposition_4_9_canonicalTriplet_right_mono :
    ∀ {n : ℕ} {c : VirtualHand n}, Meldable c → ∀ (r : Spec.Moving.Start n),
    Spec.canonicalTriplet c (Spec.Moving.rankAt r 0) = 0 → Meldable (Spec.Moving.right c
    r) → ∀ (i : Rank n), Spec.canonicalTriplet c i ≤ Spec.canonicalTriplet
    (Spec.Moving.right c r) i := by
  simpa only [Bridges.canonicalTriplet_eq, Bridges.rankAt_eq, Bridges.right_eq] using
    (@Mahjong.VirtualHand.Moving.canonicalTriplet_right_mono)

/-! Paper Proposition 4.10
https://arxiv.org/html/2611.06944v1#S4.Thmcounter10 -/

theorem proposition_4_10_consecutive_class :
    ∀ {n : ℕ} {c : VirtualHand n} {i q j : Rank n}, DrawPair c i q → DrawPair c q j →
    rankClass i = rankClass j := by
  exact @Mahjong.VirtualHand.DrawPair.consecutive_class

theorem proposition_4_10_consecutive :
    ∀ {n : ℕ} {c : VirtualHand n} {i q j : Rank n},
      DrawPair c i q → DrawPair c q j → ∃ r : Rank n,
        (min i.val j.val ≤ r.val ∧ r.val ≤ max i.val j.val) ∧
          rankClass r = rankClass i ∧ DrawPair c r q ∧ DrawPair c q r := by
  exact @Mahjong.VirtualHand.DrawPair.consecutive

/-! Paper Proposition 4.11
Proposition 4.11 (Two-pair decomposition of full-sided waits).
https://arxiv.org/html/2611.06944v1#S4.Thmcounter11 -/

theorem proposition_4_11_incoming_mutual :
    ∀ {n m : ℕ} {c : VirtualHand n} {q : Rank n}, IsFullWait m c → (∃ i, DrawPair c i q) →
    ∃ r, DrawPair c q r ∧ DrawPair c r q := by
  exact @Mahjong.VirtualHand.IsFullWait.incoming_mutual

theorem proposition_4_11_twoPair_at :
    ∀ {n m : ℕ} {c : VirtualHand n} {q : Rank n}, IsFullWait m c → rankClass q ≠
    Spec.fixedClass c → (∃ i, DrawPair c i q) → ∃ r, Spec.TwoPair c q r ∧ MeldableWith (m
    - 1) (c - pair q - pair r) := by
  exact @Mahjong.VirtualHand.IsFullWait.twoPair_at

theorem proposition_4_11_exists_twoPair :
    ∀ {n m : ℕ} {c : VirtualHand n}, IsFullWait m c → ∃ p q, rankClass p ≠ Spec.fixedClass
    c ∧ rankClass q ≠ Spec.fixedClass c ∧ rankClass p ≠ rankClass q ∧ Spec.TwoPair c p q ∧
    MeldableWith (m - 1) (c - pair p - pair q) := by
  exact @Mahjong.VirtualHand.IsFullWait.exists_twoPair

theorem proposition_4_11_remainder_meldableWith :
    ∀ {n m : ℕ} {c : VirtualHand n} {p q : Rank n},
      Spec.TwoPair c p q → size c = 3 * (m : ℤ) + 1 →
        MeldableWith (m - 1) (c - pair p - pair q) := by
  exact @Mahjong.VirtualHand.TwoPair.remainder_meldableWith

-- Unnumbered remark after 4.11: formalized.
-- See paper.json for the public source and declaration correspondence.

theorem remark_4_11_nonunique_twoPair :
    IsFullWait 4 Spec.Examples.largeHand ∧
      Spec.TwoPair Spec.Examples.largeHand (1 : Rank 2) 3 ∧
      Spec.TwoPair Spec.Examples.largeHand (3 : Rank 2) 4 ∧
      Spec.Examples.largeHand = pair (1 : Rank 2) + pair 3 +
        (2 : ℤ) • VirtualHand.sequence (2 : Fin 4) + triplet 5 ∧
      Spec.Examples.largeHand = pair (3 : Rank 2) + pair 4 +
        (2 : ℤ) • VirtualHand.sequence (1 : Fin 4) + triplet 5 ∧
      ∀ i : Rank 2, DrawPair Spec.Examples.largeHand i (![4, 3, 5, 1, 3, 5] i) := by
  refine ⟨Mahjong.Examples.largeHand_isFullWait,
    Mahjong.Examples.largeHand_twoPair_left, Mahjong.Examples.largeHand_twoPair_right,
    by decide +kernel, by decide +kernel, ?_⟩
  intro i
  fin_cases i <;> rw [DrawPair, meldable_iff_tripletGreedy] <;> decide +kernel

theorem remark_4_11_fixed_no_loop :
    IsFullWait 7 Spec.Examples.fixedNoLoop ∧ Spec.fixedClass Spec.Examples.fixedNoLoop = 0 ∧
      (∀ i : Rank 3, DrawPair Spec.Examples.fixedNoLoop i 8 ↔ i = 2 ∨ i = 5) ∧
      ¬DrawPair Spec.Examples.fixedNoLoop (8 : Rank 3) 8 := by
  exact ⟨Mahjong.Examples.fixedNoLoop_isFullWait,
    Mahjong.Examples.fixedNoLoop_fixedClass, Mahjong.Examples.fixedNoLoop_incoming,
    Mahjong.Examples.fixedNoLoop_no_self⟩

/-! Paper Proposition 5.1
Proposition 5.1 (Split at a missing rank).
https://arxiv.org/html/2611.06944v1#S5.Thmcounter1 -/

theorem proposition_5_1_meldable_split :
    ∀ {n : ℕ} {c : VirtualHand n} (k : Rank n), c k = 0 →
      (Meldable c ↔ Meldable (Spec.leftOf k c) ∧ Meldable (Spec.rightOf k c)) := by
  exact @Mahjong.VirtualHand.meldable_split

/-! Paper Proposition 5.2
https://arxiv.org/html/2611.06944v1#S5.Thmcounter2 -/

theorem proposition_5_2_missing_side_sizes :
    ∀ {n : ℕ} {c : VirtualHand n} {k a b p q : Rank n},
      c k = 0 → DrawPair c a p → DrawPair c b q → a.val < k.val → k.val < b.val →
        size (Spec.leftOf k c) % 3 = 2 ∧ size (Spec.rightOf k c) % 3 = 2 := by
  exact @Mahjong.VirtualHand.missing_side_sizes

theorem proposition_5_2_across_missing_left :
    ∀ {n : ℕ} {c : VirtualHand n} {i j k : Rank n},
      DrawPair c i j → c k = 0 → size (Spec.leftOf k c) % 3 = 2 → i.val < k.val →
        k.val < j.val ∧ Meldable (Spec.leftOf k c + single i) ∧
          rankClass i = -(rankSum (Spec.leftOf k c) : ZMod 3) := by
  exact @Mahjong.VirtualHand.DrawPair.across_missing_left

theorem proposition_5_2_across_missing_right :
    ∀ {n : ℕ} {c : VirtualHand n} {i j k : Rank n},
      DrawPair c i j → c k = 0 → size (Spec.rightOf k c) % 3 = 2 → k.val < i.val →
        j.val < k.val ∧ Meldable (Spec.rightOf k c + single i) ∧
          rankClass i = -(rankSum (Spec.rightOf k c) : ZMod 3) := by
  exact @Mahjong.VirtualHand.DrawPair.across_missing_right

/-! Paper Proposition 5.3
Proposition 5.3 (Interior positivity).
https://arxiv.org/html/2611.06944v1#S5.Thmcounter3 -/

theorem proposition_5_3_interior_positive :
    ∀ {n m : ℕ} {c : VirtualHand n}, IsFullWait m c →
      ∀ k : Rank n, 0 < k.val → k.val + 1 < 3 * n → 1 ≤ c k := by
  exact @Mahjong.VirtualHand.IsFullWait.interior_positive

/-! Paper Definition 5.4
https://arxiv.org/html/2611.06944v1#S5.Thmcounter4 -/

-- Model: Rank; Spec.interiorOnes; boundary rank indices 0 and 3*n-1.

theorem definition_5_4_classSize_const :
    ∀ {n : ℕ} (r : ZMod 3) (z : ℤ), classSize r (fun _ : Rank n => z) = (n : ℤ) * z := by
  exact @Mahjong.VirtualHand.classSize_const

theorem definition_5_4_classSize_interiorOnes :
    ∀ {n : ℕ}, 0 < n → ∀ r : ZMod 3, classSize r (Spec.interiorOnes (n := n)) =
      ((n : ℤ) - if r = 1 then 1 else 0) - if r = 0 then 1 else 0 := by
  exact @Mahjong.VirtualHand.classSize_interiorOnes

/-! Paper Proposition 5.5
https://arxiv.org/html/2611.06944v1#S5.Thmcounter5 -/

theorem proposition_5_5_incoming_both_sides :
    ∀ {n : ℕ} {c : VirtualHand n} {j a b : Rank n},
      DrawPair c a j → DrawPair c b j → a.val < j.val → j.val < b.val → 3 ≤ c j := by
  exact @Mahjong.VirtualHand.DrawPair.incoming_both_sides

/-! Paper Proposition 5.6
Proposition 5.6 (Lower bounds on congruence class sizes).
https://arxiv.org/html/2611.06944v1#S5.Thmcounter6 -/

theorem proposition_5_6_fixed_class_size :
    ∀ {n m : ℕ} {c : VirtualHand n},
      IsFullWait m c → (n : ℤ) ≤ classSize (Spec.fixedClass c) c := by
  exact @Mahjong.VirtualHand.IsFullWait.fixed_class_size

theorem proposition_5_6_nonfixed_class_size :
    ∀ {n m : ℕ} {c : VirtualHand n}, IsFullWait m c → ∀ r : ZMod 3, r ≠ Spec.fixedClass c →
      (n : ℤ) + 1 ≤ classSize r c := by
  exact @Mahjong.VirtualHand.IsFullWait.nonfixed_class_size

-- Unnumbered remark after 5.6: formalized.
-- See paper.json for the public source and declaration correspondence.

theorem remark_5_6_A_classSizes :
    ∀ {n : ℕ}, 0 < n → Spec.fixedClass (Spec.Standard.A n) = 2 ∧
      classSize 0 (Spec.Standard.A n) = (n : ℤ) + 2 ∧
      classSize 1 (Spec.Standard.A n) = (n : ℤ) + 2 ∧
      classSize 2 (Spec.Standard.A n) = (n : ℤ) := by
  intro n positive
  exact ⟨Standard.fixedClass_A positive, Standard.A_classSizes positive⟩

theorem remark_5_6_sharpness_coordinates :
    ∀ {n : ℕ}, 2 ≤ n → ∀ i : Rank n,
      Spec.ClassBoundSharpness.hand n i = if i.val = 0 then 0 else
        if i.val ≤ 3 ∨ i.val + 1 = 3 * n then 3 else 1 := by
  exact @ClassBoundSharpness.hand_apply

theorem remark_5_6_sharpness :
    ∀ {n : ℕ}, 2 ≤ n →
      IsFullWait (n + 2) (Spec.ClassBoundSharpness.hand n) ∧
      Spec.fixedClass (Spec.ClassBoundSharpness.hand n) = 2 ∧
      classSize 1 (Spec.ClassBoundSharpness.hand n) = (n : ℤ) + 1 ∧
      (∀ i fourth : Rank n, rankClass i = 0 → fourth.val = 3 →
        DrawPair (Spec.ClassBoundSharpness.hand n) i fourth) ∧
      (∀ i last : Rank n, rankClass i = 1 → last.val + 1 = 3 * n →
        DrawPair (Spec.ClassBoundSharpness.hand n) i last) ∧
      (∀ i : Rank n, rankClass i = 2 → DrawPair (Spec.ClassBoundSharpness.hand n) i i) ∧
      IsFullWait (n + 2) (reverse (Spec.ClassBoundSharpness.hand n)) ∧
      Spec.fixedClass (reverse (Spec.ClassBoundSharpness.hand n)) = 2 ∧
      classSize 0 (reverse (Spec.ClassBoundSharpness.hand n)) = (n : ℤ) + 1 := by
  intro n order
  exact ⟨ClassBoundSharpness.full order, ClassBoundSharpness.fixedClass_hand order,
    ClassBoundSharpness.classSize_one order, ClassBoundSharpness.drawPair_fourth order,
    ClassBoundSharpness.drawPair_last order, ClassBoundSharpness.drawPair_self order,
    ClassBoundSharpness.reverse_sharp order⟩

theorem remark_5_6_orderOne :
    IsFullWait 2 Spec.Examples.orderOneMiddleTriple ∧
      Spec.fixedClass Spec.Examples.orderOneMiddleTriple = 2 ∧
      classSize 0 Spec.Examples.orderOneMiddleTriple = 2 ∧
      classSize 1 Spec.Examples.orderOneMiddleTriple = 2 ∧
      classSize 2 Spec.Examples.orderOneMiddleTriple = 3 := by
  exact ⟨Mahjong.Examples.orderOneMiddleTriple_isFullWait,
    Mahjong.Examples.orderOneMiddleTriple_fixedClass,
    Mahjong.Examples.orderOneMiddleTriple_classSizes⟩

/-! Paper Proposition 5.7
https://arxiv.org/html/2611.06944v1#S5.Thmcounter7 -/

theorem proposition_5_7_meldCount_gt_order :
    ∀ {n m : ℕ} {c : VirtualHand n}, IsFullWait m c → n < m := by
  exact @Mahjong.VirtualHand.IsFullWait.meldCount_gt_order

/-! Paper Proposition 5.8
Proposition 5.8 (Sizes of congruence classes).
https://arxiv.org/html/2611.06944v1#S5.Thmcounter8 -/

theorem proposition_5_8_fixed_class_size_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → IsFullWait (n + 1) c →
      classSize (Spec.fixedClass c) c = (n : ℤ) := by
  exact @Mahjong.VirtualHand.IsFullWait.fixed_class_size_succ

theorem proposition_5_8_nonfixed_class_size_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → IsFullWait (n + 1) c →
      ∀ r : ZMod 3, r ≠ Spec.fixedClass c → classSize r c = (n : ℤ) + 2 := by
  exact @Mahjong.VirtualHand.IsFullWait.nonfixed_class_size_succ

-- Unnumbered remark after 5.8: formalized.
-- See paper.json for the public source and declaration correspondence.

theorem remark_5_8_orderOne_exception :
    IsFullWait 2 Spec.Examples.orderOneMiddleTriple ∧
      Spec.fixedClass Spec.Examples.orderOneMiddleTriple = 2 ∧
      classSize 0 Spec.Examples.orderOneMiddleTriple = 2 ∧
      classSize 1 Spec.Examples.orderOneMiddleTriple = 2 ∧
      classSize 2 Spec.Examples.orderOneMiddleTriple = 3 := by
  exact remark_5_6_orderOne

/-! Paper Proposition 5.9
Proposition 5.9 (Two pillars).
https://arxiv.org/html/2611.06944v1#S5.Thmcounter9 -/

theorem proposition_5_9_exists_pillar :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → IsFullWait (n + 1) c → ∀ (r : ZMod 3), r ≠
    Spec.fixedClass c → ∃ p, rankClass p = r ∧ Spec.Pillar c p ∧ c p ≤ 4 := by
  exact @Mahjong.VirtualHand.IsFullWait.exists_pillar

theorem proposition_5_9_fixed_count_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → IsFullWait (n + 1) c → ∀ (i : Rank n),
    rankClass i = Spec.fixedClass c → c i ≤ 2 := by
  exact @Mahjong.VirtualHand.IsFullWait.fixed_count_succ

theorem proposition_5_9_fixed_pair_unique_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → IsFullWait (n + 1) c → ∀ {i j : Rank n},
    rankClass i = Spec.fixedClass c → rankClass j = Spec.fixedClass c → 2 ≤ c i → 2 ≤ c j
    → i = j := by
  exact @Mahjong.VirtualHand.IsFullWait.fixed_pair_unique_succ

theorem proposition_5_9_fixed_draw_placement_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, 2 ≤ n → IsFullWait (n + 1) c →
      ∀ p q : Rank n, Spec.Pillar c p → Spec.Pillar c q →
        rankClass p ≠ Spec.fixedClass c → rankClass q = Spec.pairedClass c (rankClass p) →
          ∀ {i j : Rank n}, DrawPair c i j → rankClass i = Spec.fixedClass c →
            ∀ {t : Placement n}, Placement.Nonnegative t → t.toHand = c + single i - pair j →
              Spec.Placement.sequenceCount t = (n : ℤ) - 1 ∧ t.tripNum = single p + single q := by
  exact @Mahjong.VirtualHand.IsFullWait.fixed_draw_placement_succ

-- Unnumbered remark after 5.9: formalized.
-- See paper.json for the public source and declaration correspondence.

theorem remark_5_9_D_attainment :
    ∀ {n : ℕ}, 2 ≤ n → Spec.fixedClass (Spec.Standard.D n) = 1 ∧
      ∃ i : Rank n, i.val = 3 ∧ rankClass i = Spec.fixedClass (Spec.Standard.D n) ∧
        Spec.Standard.D n i = 2 := by
  exact @Standard.D_fixed_bound_sharp

/-! Paper Proposition 5.10
Proposition 5.10 (Draw-pair relation and two-pair decomposition).
https://arxiv.org/html/2611.06944v1#S5.Thmcounter10 -/

theorem proposition_5_10 :
    ∀ {n : ℕ}, 2 ≤ n → ∀ {c : VirtualHand n}, IsFullWait (n + 1) c → ∀ p q : Rank n,
    rankClass p ≠ Spec.fixedClass c → rankClass q = Spec.pairedClass c (rankClass p) →
    Spec.Pillar c p → Spec.Pillar c q → (∀ i j : Rank n, rankClass i = rankClass p →
    (DrawPair c i j ↔ j = q)) ∧ (∀ i j : Rank n, rankClass i = rankClass q → (DrawPair c i
    j ↔ j = p)) ∧ Spec.TwoPair c p q ∧ (∀ a b : Rank n, Spec.TwoPair c a b ↔ (a = p ∧ b =
    q) ∨ (a = q ∧ b = p)) ∧ Spec.Sequential (c - pair p - pair q) ∧ size (c - pair p -
    pair q) = 3 * (n : ℤ) ∧ (∀ i : Rank n, rankClass i = rankClass p → Spec.Sequential
    (Spec.moveTile (c - pair p - pair q) p i)) ∧ (∀ i : Rank n, rankClass i = rankClass q
    → Spec.Sequential (Spec.moveTile (c - pair p - pair q) q i)) := by
  intro n order c full p q nonfixed class_q pillar_p pillar_q
  let pillars : Pillars c p q := ⟨nonfixed, class_q, pillar_p, pillar_q⟩
  have remainder := pillars.remainder_sequential_moves_succ order full
  exact ⟨fun _ _ same ↦ pillars.drawPair_iff full same,
    fun _ _ same ↦ pillars.swap.drawPair_iff full same,
    pillars.twoPair full, fun a b ↦ pillars.twoPair_iff order full a b,
    remainder.1, remainder.2.1, remainder.2.2.1, remainder.2.2.2⟩

-- Unnumbered remark after 5.10: formalized.
-- See paper.json for the public source and declaration correspondence.

theorem remark_5_10_difference :
    ∀ {n m k : ℕ} {c d : VirtualHand n}, IsFullWait m c → IsFullWait k d →
      (VirtuallyMeldable (c - d) ↔ Spec.fixedClass c = Spec.fixedClass d) := by
  exact @IsFullWait.virtuallyMeldable_sub_iff

theorem remark_5_10_partition :
    ∀ {n : ℕ}, 2 ≤ n → ∀ {c : VirtualHand n}, Spec.Standard.EightFamily c →
      (Spec.fixedClass c = 2 ↔ c = Spec.Standard.A n ∨ c = Spec.Standard.B n ∨
        c = Spec.Standard.B' n ∨ c = Spec.Standard.E n) ∧
      (Spec.fixedClass c = 1 ↔ c = Spec.Standard.C n ∨ c = Spec.Standard.D n) ∧
      (Spec.fixedClass c = 0 ↔ c = Spec.Standard.C' n ∨ c = Spec.Standard.D' n) := by
  exact @Standard.fixedClass_partition

/-! Paper Problem 6.1
https://arxiv.org/html/2611.06944v1#S6.Thmcounter1 -/

-- OPEN PROBLEM: Classify and count full-sided waits for m>n+1, especially m=n+2.
-- No theorem assumption or verified target is introduced.

/-! Paper Proposition 6.2
Proposition 6.2 (Abundance of full-sided waits).
https://arxiv.org/html/2611.06944v1#S6.Thmcounter2 -/

theorem proposition_6_2_drawPair_of_abundant :
    ∀ {n : ℕ} {c : VirtualHand n}, (size c : ZMod 3) = 1 → Spec.abundanceThreshold ≤ c →
      ∀ i j : Rank n, rankClass i + rankClass j = -(rankSum c : ZMod 3) → DrawPair c i j := by
  exact @Mahjong.VirtualHand.drawPair_of_abundant

theorem proposition_6_2_isFullWait_of_abundant :
    ∀ {n m : ℕ} {c : VirtualHand n}, 0 < n → Spec.abundanceThreshold ≤ c →
      size c = 3 * (m : ℤ) + 1 → IsFullWait m c := by
  exact @Mahjong.VirtualHand.isFullWait_of_abundant

theorem proposition_6_2_exists_full :
    ∀ {n : ℕ}, 0 < n → ∀ c : VirtualHand n, Nonnegative c → (size c : ZMod 3) = 1 →
    Spec.abundanceThreshold ≤ c → ∃ m, IsFullWait m c := by
  intro n order c positive residue large
  have nonnegative := positive.size_nonnegative
  have remainder := (ZMod.intCast_eq_intCast_iff' (size c) 1 3).mp residue
  norm_num only [Nat.cast_ofNat, Int.one_emod] at remainder
  let m : ℕ := (size c / 3).toNat
  have count : size c = 3 * (m : ℤ) + 1 := by dsimp [m]; omega
  exact ⟨m, isFullWait_of_abundant order large count⟩

/-! Paper Definition 6.3
Definition 6.3 (Minimal full-sided wait).
https://arxiv.org/html/2611.06944v1#S6.Thmcounter3 -/

-- Model: IsMinimalFullWait (arbitrary nonzero meldable removals).

/-! Paper Problem 6.4
https://arxiv.org/html/2611.06944v1#S6.Thmcounter4 -/

-- OPEN PROBLEM: Classify and count all minimal full-sided waits for arbitrary n and m.
-- No theorem assumption or verified target is introduced.

/-! Paper Example 6.5
Example 6.5 (Standard Mahjong).
https://arxiv.org/html/2611.06944v1#S6.Thmcounter5 -/

theorem example_6_5_minimal_succ :
    ∀ {n : ℕ} {c : VirtualHand n}, IsFullWait (n + 1) c → IsMinimalFullWait (n + 1) c := by
  exact @Mahjong.VirtualHand.IsFullWait.minimal_succ

theorem example_6_5_minimalFullWait_card_zero :
    ∀ {n m : ℕ}, m ≤ n → Nat.card { c : VirtualHand n // IsMinimalFullWait m c } = 0 := by
  exact @Mahjong.VirtualHand.minimalFullWait_card_zero

theorem example_6_5_minimalFullWait_card_eight :
    ∀ {n : ℕ}, 2 ≤ n → Nat.card { c : VirtualHand n // IsMinimalFullWait (n + 1) c } = 8 := by
  exact @Mahjong.VirtualHand.minimalFullWait_card_eight

theorem example_6_5_minimalFullWait_card_six :
    Nat.card { c : VirtualHand 1 // IsMinimalFullWait 2 c } = 6 := by
  exact @Mahjong.VirtualHand.minimalFullWait_card_six

/-! Paper Example 6.6
Example 6.6 (Taiwanese Mahjong).
https://arxiv.org/html/2611.06944v1#S6.Thmcounter6 -/

-- DEFERRED: total/live/minimal counts 149/11/27 have no Lean proof here.
-- No solution declaration; this result is excluded from config.json.

/-! Paper Proposition 6.7
https://arxiv.org/html/2611.06944v1#S6.Thmcounter7 -/

theorem proposition_6_7_orderOne_isMinimalFullWait_iff :
    ∀ {m : ℕ} {c : VirtualHand 1}, IsMinimalFullWait m c ↔ m = 2 ∧
    Spec.Standard.OrderOneFamily c := by
  exact @Mahjong.VirtualHand.orderOne_isMinimalFullWait_iff

theorem proposition_6_7_orderOne_allMinimalFullWait_card :
    Nat.card { c : VirtualHand 1 // ∃ m, IsMinimalFullWait m c } = 6 := by
  exact @Mahjong.VirtualHand.orderOne_allMinimalFullWait_card

/-! Paper Proposition 6.8
https://arxiv.org/html/2611.06944v1#S6.Thmcounter8 -/

theorem proposition_6_8_exists_maximal_minimal_meldCount :
    ∀ {n : ℕ}, 0 < n → ∃ M, (∃ (c : VirtualHand n), IsMinimalFullWait M c) ∧ (∀ {m : ℕ} {c
    : VirtualHand n}, IsMinimalFullWait m c → m ≤ M) ∧ 2 * n ≤ M ∧ M < 8 * n := by
  exact @Mahjong.VirtualHand.exists_maximal_minimal_meldCount

/-! Paper Conjecture 6.9
https://arxiv.org/html/2611.06944v1#S6.Thmcounter9 -/

-- OPEN CONJECTURE: M(1)=2 is proved; the equality for n>=2 remains open.
-- This is a proposition definition, not an assumption or a verified target.
def conjecture_6_9 : Prop :=
  Spec.maxMinimalMeldCount 1 = 2 ∧
    ∀ n : ℕ, 2 ≤ n → Spec.maxMinimalMeldCount n = 9 * n / 2 - 3

/-! Additional formalized results (not assigned a theorem number in arXiv v1). -/

theorem alternating_even (a : ℕ) :
    IsFullWait (9 * a + 6) (Spec.AlternatingWait.even a) :=
  AlternatingWait.even_full a

theorem alternating_odd (a : ℕ) :
    IsFullWait (9 * a + 10) (Spec.AlternatingWait.odd a) :=
  AlternatingWait.odd_full a

theorem alternating_even_minimal (a : ℕ) :
    IsMinimalFullWait (9 * a + 6) (Spec.AlternatingWait.even a) :=
  AlternatingWait.even_minimal a

theorem alternating_odd_minimal (a : ℕ) :
    IsMinimalFullWait (9 * a + 10) (Spec.AlternatingWait.odd a) :=
  AlternatingWait.odd_minimal a

theorem maximal_minimal_wait_strong (n : ℕ) (positive : 0 < n) :
    ∃ M : ℕ, (∃ c : VirtualHand n, IsMinimalFullWait M c) ∧
      (∀ (m : ℕ) (c : VirtualHand n), IsMinimalFullWait m c → m ≤ M) ∧
        max (2 * n) (9 * n / 2 - 3) ≤ M ∧ M < 8 * n :=
  ⟨maxMinimalMeldCount n, exists_minimal_at_max positive, fun _ _ h ↦ h.le_max,
    maxMinimalMeldCount_strong_bounds positive⟩

theorem taiwanese_nonminimal_cardinality :
    Nat.card {c : VirtualHand 3 // IsFullWait 5 c ∧ ¬IsMinimalFullWait 5 c} = 122 :=
  taiwanese_nonminimal_card

/-! Further consequences in this development, beyond the numbered public v1 results. -/

theorem next_live_nonminimal_classification :
    ∀ {n : ℕ}, 2 ≤ n → ∀ c : VirtualHand n,
      (IsLiveFullWait 4 (n + 2) c ∧ ¬IsMinimalFullWait (n + 2) c) ↔
        ∃ r : Fin (3 * n - 2), 0 < r.val ∧ r.val + 3 < 3 * n ∧
          c = Spec.Standard.A n + VirtualHand.sequence r := by
  exact @Mahjong.VirtualHand.next_live_not_minimal_iff

theorem next_live_nonminimal_cardinality :
    ∀ {n : ℕ}, 2 ≤ n →
      Nat.card {c : VirtualHand n // IsLiveFullWait 4 (n + 2) c ∧
        ¬IsMinimalFullWait (n + 2) c} = 3 * n - 4 := by
  exact @Mahjong.VirtualHand.next_live_nonminimal_card

theorem sharpness_minimal_live :
    ∀ {n : ℕ}, 2 ≤ n →
      IsMinimalFullWait (n + 2) (Spec.ClassBoundSharpness.hand n) ∧
        IsLiveFullWait 4 (n + 2) (Spec.ClassBoundSharpness.hand n) := by
  intro n order
  exact ⟨ClassBoundSharpness.minimal order, ClassBoundSharpness.live order⟩

/-! Order-one full waits for arbitrary meld count: a further structural consequence.
The subtraction in the cardinality formula is natural subtraction; the count
is zero for m<=1 and the usual binomial coefficient for m>=2. -/

theorem orderOne_full_criterion :
    ∀ {m : ℕ} (c : VirtualHand 1), IsFullWait m c ↔
      size c = 3 * (m : ℤ) + 1 ∧
        ∀ i : Rank 1, (if rankClass i = Spec.fixedClass c then (1 : ℤ) else 2) ≤ c i := by
  exact @Mahjong.VirtualHand.OrderOne.full_iff

theorem orderOne_full_cardinality :
    ∀ m : ℕ, Nat.card {c : VirtualHand 1 // IsFullWait m c} = Nat.choose (3 * m - 2) 2 := by
  exact Mahjong.VirtualHand.orderOne_fullWait_card

end ComparatorChallenges
