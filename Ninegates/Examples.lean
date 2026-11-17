/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Wait.Basic
public import Ninegates.Meldable.ClosedForm

/-!
# A full wait beyond the old fixed meld count

The paper's `(0, 2, 2, 4, 2, 3)` is a full-sided `(2, 4)`-wait. Explicit meld
placements verify each draw, without a decision procedure for meldability.
The same hand is live with five copies, but not with four copies.
An example with a negative sequence coefficient checks the Euclidean-division
and zero-extension conventions in virtual canonicalization.
-/

@[expose] public section

namespace Mahjong.Examples

open VirtualHand

def largeHand : VirtualHand 2 := ![0, 2, 2, 4, 2, 3]

private def eye : Rank 2 → Rank 2 := ![4, 3, 5, 1, 3, 5]
private def sequences : Rank 2 → Fin 4 → ℤ :=
  ![![1, 1, 0, 0], ![0, 0, 2, 0], ![0, 2, 1, 1],
    ![0, 0, 2, 0], ![0, 2, 0, 0], ![0, 2, 0, 2]]
private def triplets : Rank 2 → Rank 2 → ℤ :=
  ![![0, 0, 0, 1, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0]]

private lemma drawPair (i : Rank 2) : DrawPair largeHand i (eye i) := by
  refine ⟨⟨sequences i, triplets i⟩, ?_, ?_⟩
  · constructor <;> intro j <;> fin_cases i <;> fin_cases j <;>
      norm_num [sequences, triplets]
  · ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [Placement.toHand, sequences, triplets, VirtualHand.sequence, triplet, pair,
        VirtualHand.single, largeHand, eye, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]

lemma largeHand_isFullWait : IsFullWait 4 largeHand := by
  rw [isFullWait_iff]
  refine ⟨?_, ?_, fun i ↦ ⟨eye i, drawPair i⟩⟩
  · intro i
    fin_cases i <;> norm_num [largeHand]
  · norm_num [size, largeHand, Fin.sum_univ_succ]

lemma largeHand_not_live_four : ¬IsLiveFullWait 4 4 largeHand := by
  intro live
  have bound := (isLiveFullWait_iff.mp live).2 (3 : Rank 2)
  norm_num [largeHand] at bound

lemma largeHand_live_five : IsLiveFullWait 5 4 largeHand := by
  rw [isLiveFullWait_iff]
  refine ⟨largeHand_isFullWait, ?_⟩
  intro i
  fin_cases i <;> norm_num [largeHand]

def negativeSequence : Placement 2 := ⟨![-1, 0, 0, 0], 0⟩

lemma negativeSequence_canonicalize : negativeSequence.canonicalize =
    (⟨![2, 0, 0, 0], ![-1, -1, -1, 0, 0, 0]⟩ : Placement 2) := by
  apply Placement.ext <;> ext i <;> fin_cases i <;>
    norm_num [negativeSequence, Placement.canonicalize, coefficient]

lemma negativeSequence_not_meldable : ¬Meldable negativeSequence.toHand := by
  intro meldable
  have normalized : Meldable negativeSequence.canonicalize.toHand := by simpa using meldable
  have nonnegative := negativeSequence.canonic_canonicalize.meldable_iff_tripNum_nonnegative.mp
    normalized
  have at_zero := nonnegative (0 : Rank 2)
  rw [negativeSequence_canonicalize] at at_zero
  norm_num at at_zero

/-- Neither of the two right-end conditions may be dropped. These hands have
zero coefficients at every admissible sequence start, but nonzero scan tails. -/
def lastTile : VirtualHand 2 := single 5
def lastTwoTiles : VirtualHand 2 := single 4 + single 5

lemma recoveredSequences_lastTile : recoveredSequences lastTile = 0 := by
  ext i
  fin_cases i <;> norm_num [recoveredSequences, sequenceScan, SequenceScan.run,
    lastTile, coefficient, single]

lemma recoveredSequences_lastTwoTiles : recoveredSequences lastTwoTiles = 0 := by
  ext i
  fin_cases i <;> norm_num [recoveredSequences, sequenceScan, SequenceScan.run,
    lastTwoTiles, coefficient, single]

lemma sequenceScan_lastTile : sequenceScan lastTile 6 = (1, 0) := by decide +kernel
lemma sequenceScan_lastTwoTiles : sequenceScan lastTwoTiles 6 = (0, 1) := by decide +kernel

lemma lastTile_not_virtuallySequential : ¬VirtuallySequential lastTile := by
  rw [virtuallySequential_iff_scan, sequenceScan_lastTile]
  norm_num

lemma lastTwoTiles_not_virtuallySequential : ¬VirtuallySequential lastTwoTiles := by
  rw [virtuallySequential_iff_scan, sequenceScan_lastTwoTiles]
  norm_num

/-- Both tail obstructions above occur even though all triplet quotients are zero. -/
lemma canonicalTriplets_lastTile : ∀ i, canonicalTriplet lastTile i = 0 := by
  intro i
  fin_cases i <;> norm_num [canonicalTriplet, canonicalSequence, sequenceScan,
    SequenceScan.run, lastTile, coefficient, single]

lemma canonicalTriplets_lastTwoTiles : ∀ i, canonicalTriplet lastTwoTiles i = 0 := by
  intro i
  fin_cases i <;> norm_num [canonicalTriplet, canonicalSequence, sequenceScan,
    SequenceScan.run, lastTwoTiles, coefficient, single]

/-- Size and rank-sum congruences alone do not ensure actual meldability. -/
def spacedTiles : VirtualHand 2 := single 0 + single 2 + single 4

lemma spacedTiles_nonnegative : Nonnegative spacedTiles :=
  ((nonnegative_single _).add (nonnegative_single _)).add (nonnegative_single _)

lemma spacedTiles_virtuallyMeldable : VirtuallyMeldable spacedTiles := by
  rw [virtuallyMeldable_iff_size_rankSum]
  decide +kernel

lemma canonicalTriplet_spacedTiles : canonicalTriplet spacedTiles (1 : Rank 2) = -1 := by
  decide +kernel

lemma spacedTiles_not_meldable : ¬Meldable spacedTiles := by
  intro meldable
  have bound := ((meldable_iff_scan spacedTiles).mp meldable).2 (1 : Rank 2)
  rw [canonicalTriplet_spacedTiles] at bound
  omega

end Mahjong.Examples
