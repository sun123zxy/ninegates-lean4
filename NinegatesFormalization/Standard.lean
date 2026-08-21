import NinegatesFormalization.Winning
import NinegatesFormalization.Meldable.Basic

namespace Mahjong.Hand

@[grind =]
def standardFullWait (n : ℕ) (hn : 0 < n) : Hand n :=
  ⟨fun i ↦ if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1⟩

@[simp, grind =]
lemma size_standardFullWait (n : ℕ) (hn : 0 < n) :
    size (standardFullWait n hn) = 3 * n + 4 := by
  change (∑ i : Fin (3 * n), if i.val = 0 ∨
      i.val = 3 * n - 1 then 3 else 1) = 3 * n + 4
  classical
  have hsplit (i : Fin (3 * n)) :
      (if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1) =
        1 + (if i.val = 0 then 2 else 0) +
          (if i.val = 3 * n - 1 then 2 else 0) := by
    grind
  have hzero :
      (∑ i : Fin (3 * n), if i.val = 0 then 2 else 0) = 2 := by
    let z : Fin (3 * n) := ⟨0, by omega⟩
    rw [Finset.sum_eq_single z]
    · simp [z]
    · intro i hi hne
      by_cases hi0 : i.val = 0
      · exfalso
        apply hne
        apply Fin.ext
        simpa [z] using hi0
      · simp [hi0]
    · simp
  have hlast :
      (∑ i : Fin (3 * n), if i.val = 3 * n - 1 then 2 else 0) = 2 := by
    let l : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
    rw [Finset.sum_eq_single l]
    · simp [l]
    · intro i hi hne
      by_cases hil : i.val = 3 * n - 1
      · exfalso
        apply hne
        apply Fin.ext
        simpa [l] using hil
      · simp [hil]
    · simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    hzero, hlast]
  simp [Fintype.card_fin]

@[simp, grind =]
lemma standardFullWait_apply (n : ℕ) (hn : 0 < n) (i : Fin (3 * n)) :
    standardFullWait n hn i =
      if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1 := by
  rfl

set_option maxHeartbeats 1000000 in
-- The explicit residue cases keep the remaining arithmetic automation bounded.
theorem IsFullWait.standardFullWait (n : ℕ) (hn : 0 < n) :
    IsFullWait (standardFullWait n hn) := by
  intro p
  split_ands
  · intro i
    simp only [add_apply, standardFullWait_apply, single_apply]
    split_ifs <;> omega
  · rw [map_add, size_single, size_standardFullWait]
  · have hmod : p.val % 3 = 0 ∨ p.val % 3 = 1 ∨ p.val % 3 = 2 := by grind only
    rcases hmod with h | h | h
    · let tsm : Hand n := ⟨fun i ↦ if i.val = 0 then 0 else 1⟩
      let sm : Hand n := ⟨fun i ↦ if i.val = 0 then 3 else 1⟩
      let q : Meldable.Placement n :=
        ⟨0, fun i ↦ if i.val + 2 < 3 * n ∧
          ((i.val % 3 = 1 ∧ i.val < p.val) ∨
            (i.val % 3 = 0 ∧ p.val ≤ i.val)) then 1 else 0, by
            constructor <;> intro i hi <;>
              simp only [ite_eq_right_iff] <;> intro h <;> grind⟩
      have hq : q.toHand = tsm + single p := by
        apply Hand.ext
        intro i
        simp only [Meldable.Placement.toHand_apply, add_apply, single_apply]
        have htsm : tsm i = if i.val = 0 then 0 else 1 := by
          rfl
        rw [htsm]
        dsimp [q]
        simp only [zero_add]
        have hm0 (x : ℕ) (hx : x % 3 = 0) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 2 ∧ (x - 2) % 3 = 1 := by omega
        have hm1 (x : ℕ) (hx : x % 3 = 1) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 0 ∧ (x - 2) % 3 = 2 := by omega
        have hm2 (x : ℕ) (hx : x % 3 = 2) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 1 ∧ (x - 2) % 3 = 0 := by omega
        have himod : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
        rcases himod with hi0 | hi1 | hi2
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm0 i.val hi0 (by omega)
            split_ifs <;> omega
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm1 i.val hi1 (by omega)
            split_ifs <;> omega
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm2 i.val hi2 (by omega)
            split_ifs <;> omega
      have hsm : sm + pair ⟨3 * n - 1, by omega⟩ = Mahjong.Hand.standardFullWait n hn := by
        apply Hand.ext
        intro i
        simp only [add_apply, pair_apply, standardFullWait_apply]
        have hsm_i : sm i = if i.val = 0 then 3 else 1 := by
          rfl
        rw [hsm_i]
        split_ifs <;> omega
      have htsm : tsm + triplet ⟨0, by omega⟩ = sm := by
        apply Hand.ext
        intro i
        simp only [add_apply, triplet_apply]
        have htsm_i : tsm i = if i.val = 0 then 0 else 1 := by
          rfl
        have hsm_i : sm i = if i.val = 0 then 3 else 1 := by
          rfl
        rw [htsm_i, hsm_i]
        split_ifs <;> omega
      refine ⟨q.toHand + triplet ⟨0, by omega⟩, ⟨3 * n - 1, by omega⟩, ?_⟩
      constructor
      · exact Meldable.add ⟨q, rfl⟩ (Meldable.triplet)
      · rw [hq]
        rw [← hsm, ← htsm]
        ac_rfl
    · let q : Meldable.Placement n := -- this requires a larger heartbeat limit
        ⟨(fun i ↦ if i.val = 0 ∨
            i.val = 3 * n - 1 then 1 else 0),
          fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 1 ∧ i.val < p.val) ∨
              (i.val % 3 = 2 ∧ p.val < i.val)) then 1 else 0, by
            constructor <;> intro i hi <;>
              simp only [ite_eq_right_iff] <;> intro h <;> grind⟩
      refine ⟨q.toHand, p, ?_⟩
      constructor
      · exact ⟨q, rfl⟩
      · apply Hand.ext
        intro i
        simp only [Meldable.Placement.toHand_apply, standardFullWait_apply,
          add_apply, pair_apply, single_apply]
        dsimp [q]
        have hm0 (x : ℕ) (hx : x % 3 = 0) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 2 ∧ (x - 2) % 3 = 1 := by omega
        have hm1 (x : ℕ) (hx : x % 3 = 1) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 0 ∧ (x - 2) % 3 = 2 := by omega
        have hm2 (x : ℕ) (hx : x % 3 = 2) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 1 ∧ (x - 2) % 3 = 0 := by omega
        have himod : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
        rcases himod with hi0 | hi1 | hi2
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm0 i.val hi0 (by omega)
            split_ifs <;> omega
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm1 i.val hi1 (by omega)
            split_ifs <;> omega
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm2 i.val hi2 (by omega)
            split_ifs <;> omega
    · let q : Meldable.Placement n :=
        ⟨(fun i ↦ if i.val = 3 * n - 1 then 1 else 0),
          fun i ↦ if i.val + 2 < 3 * n ∧
            ((i.val % 3 = 0 ∧ i.val < p.val) ∨
              (i.val % 3 = 2 ∧ p.val ≤ i.val)) then 1 else 0, by
            constructor <;> intro i hi <;>
              simp only [ite_eq_right_iff] <;> intro h <;> grind⟩
      refine ⟨q.toHand, ⟨0, by omega⟩, ?_⟩
      constructor
      · exact ⟨q, rfl⟩
      · apply Hand.ext
        intro i
        simp only [Meldable.Placement.toHand_apply, standardFullWait_apply,
          add_apply, pair_apply, single_apply]
        dsimp [q]
        have hm0 (x : ℕ) (hx : x % 3 = 0) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 2 ∧ (x - 2) % 3 = 1 := by omega
        have hm1 (x : ℕ) (hx : x % 3 = 1) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 0 ∧ (x - 2) % 3 = 2 := by omega
        have hm2 (x : ℕ) (hx : x % 3 = 2) (hx2 : 2 ≤ x) :
            (x - 1) % 3 = 1 ∧ (x - 2) % 3 = 0 := by omega
        have himod : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
        rcases himod with hi0 | hi1 | hi2
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm0 i.val hi0 (by omega)
            split_ifs <;> omega
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm1 i.val hi1 (by omega)
            split_ifs <;> omega
        · by_cases hs : i.val < 2
          · split_ifs <;> omega
          · have hi := hm2 i.val hi2 (by omega)
            split_ifs <;> omega
end Mahjong.Hand
