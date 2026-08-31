import Ninegates.Wait.Decide
import Ninegates.Winning.Decidable

/-!
Correctness specifications and optimized `Decidable` instances for waits.
-/

namespace Mahjong.Hand

namespace IsWinningTile.Decidable

theorem decide_spec (c : Hand n) (i : Fin (3 * n)) :
    IsWinningTile.decide c i = true ↔ IsWinningTile c i := by
  simp [IsWinningTile.decide, IsWinningTile, Winning.Decidable.decide_spec]

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsWinningTile c i) :=
  decidable_of_iff (IsWinningTile.decide c i = true) (decide_spec c i)

end IsWinningTile.Decidable

namespace IsLiveWinningTile.Decidable

theorem decide_spec (c : Hand n) (i : Fin (3 * n)) :
    IsLiveWinningTile.decide c i = true ↔ IsLiveWinningTile c i := by
  simp only [IsLiveWinningTile.decide, IsWinningTile.decide, Bool.and_eq_true,
    Winning.Decidable.decide_spec, decide_eq_true_eq]
  rfl

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsLiveWinningTile c i) :=
  decidable_of_iff (IsLiveWinningTile.decide c i = true) (decide_spec c i)

end IsLiveWinningTile.Decidable

namespace IsFullWait.Decidable

theorem waitingTiles_size (count : Array Nat) :
    (waitingTiles count).size = count.size := by
  simp [waitingTiles]

theorem waitingTiles_spec (c : Hand n) (hc : Hand.size c = 3 * n + 4) (i : Fin (3 * n)) :
    (waitingTiles (Array.ofFn c))[i.val]'(by simp [waitingTiles_size]) = true ↔
      IsWinningTile c i := by
  sorry

end IsFullWait.Decidable

namespace IsWait.Decidable

theorem decide_spec (c : Hand n) :
    IsWait.decide c = true ↔ IsWait c := by
  simp only [IsWait.decide, Bool.and_eq_true, Array.any_eq_true, IsWait]
  constructor
  · rintro ⟨hsize, ⟨j, hj, h⟩⟩
    have hcsize : Hand.size c = 3 * n + 4 := by simpa using hsize
    let i : Fin (3 * n) := ⟨j, by simpa [IsFullWait.Decidable.waitingTiles_size] using hj⟩
    exact ⟨i, IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp h⟩
  · rintro ⟨i, hi⟩
    have hcsize := IsWait.size ⟨i, hi⟩
    refine ⟨by simpa using hcsize, i.val, ?_, ?_⟩
    · simp [IsFullWait.Decidable.waitingTiles_size]
    · exact IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mpr hi

instance (c : Hand n) : Decidable (IsWait c) :=
  decidable_of_iff (IsWait.decide c = true) (decide_spec c)

end IsWait.Decidable

namespace IsLiveWait.Decidable

theorem decide_spec (c : Hand n) :
    IsLiveWait.decide c = true ↔ IsLiveWait c := by
  simp only [IsLiveWait.decide, Bool.and_eq_true, Array.all_eq_true,
    Array.any_eq_true]
  constructor
  · rintro ⟨⟨hsize, hvalid⟩, ⟨j, hj, hRaw⟩⟩
    have hcsize : Hand.size c = 3 * n + 4 := by simpa using hsize
    have hRaw' := hRaw
    simp only [id_eq, Array.getElem_zipWith hj, Array.getElem_map] at hRaw'
    rcases Bool.and_eq_true_iff.mp hRaw' with ⟨hwaitRaw, hcountRaw⟩
    let i : Fin (3 * n) := ⟨j, by
      have := hj
      have h' : j < 3 * n := by
        simpa [Array.size_zipWith, Array.size_map,
          IsFullWait.Decidable.waitingTiles_size] using this
      exact h'⟩
    have hwait :
        (IsFullWait.Decidable.waitingTiles (Array.ofFn c))[i.val]'(by
          simp [IsFullWait.Decidable.waitingTiles_size]) = true := by
      simpa [i] using hwaitRaw
    have hcount : c i ≤ 3 := by
      simpa [i, Array.getElem_map] using hcountRaw
    have hvc : Valid c := by
      intro k
      have hk := hvalid k.val (by simp)
      simpa using hk
    exact ⟨i, isLiveWinningTile_iff.mpr
      ⟨IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp hwait, hvc, hcount⟩⟩
  · rintro ⟨i, hi⟩
    rcases isLiveWinningTile_iff.mp hi with ⟨hw, hvalid, hcount⟩
    have hcsize := IsLiveWait.size ⟨i, hi⟩
    refine ⟨⟨by simpa using hcsize, ?_⟩, ?_⟩
    · intro j hj
      have hj' : j < 3 * n := by simpa using hj
      have hjv := hvalid ⟨j, hj'⟩
      simpa using hjv
    · refine ⟨i.val, ?_, ?_⟩
      · simp [Array.size_zipWith,
          IsFullWait.Decidable.waitingTiles_size]
      · have hwait := IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mpr hw
        have hcnt :
            Decidable.decide ((Array.ofFn c)[i.val]'(by simp) ≤ 3) = true := by
          simpa using hcount
        simpa [id_eq, Array.getElem_zipWith, Array.getElem_map, hwait, hcnt]

instance (c : Hand n) : Decidable (IsLiveWait c) :=
  decidable_of_iff (IsLiveWait.decide c = true) (decide_spec c)

end IsLiveWait.Decidable

namespace IsFullWait.Decidable

theorem decide_spec (c : Hand n) :
    IsFullWait.decide c = true ↔ IsFullWait c := by
  cases n with
  | zero =>
    have hc : c = 0 := by
      ext i
      exact Fin.elim0 i
    subst c
    have hwt : IsFullWait.Decidable.waitingTiles (Array.ofFn (0 : Hand 0)) = #[] := by
      rfl
    simp only [IsFullWait.decide]
    rw [hwt]
    simp [IsFullWait]
  | succ n =>
    simp only [IsFullWait.decide, Bool.and_eq_true, Bool.or_eq_true,
      Array.all_eq_true, IsFullWait]
    constructor
    · rintro ⟨hsize, hwait⟩ i
      have hcsize : Hand.size c = 3 * (n + 1) + 4 := by
        have hsize' := hsize.resolve_left (by simp)
        simpa using hsize'
      have hi := hwait i.val (by simp [IsFullWait.Decidable.waitingTiles_size])
      exact IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp hi
    · intro h
      have hcsize := IsFullWait.size (Nat.succ_pos n) h
      refine ⟨Or.inr (by simpa using hcsize), ?_⟩
      intro i hi
      let j : Fin (3 * (n + 1)) := ⟨i, by
        simpa [IsFullWait.Decidable.waitingTiles_size] using hi⟩
      exact IsFullWait.Decidable.waitingTiles_spec c hcsize j |>.mpr (h j)

instance (c : Hand n) : Decidable (IsFullWait c) :=
  decidable_of_iff (IsFullWait.decide c = true) (decide_spec c)

end IsFullWait.Decidable

namespace IsLiveFullWait.Decidable

theorem decide_spec (c : Hand n) :
    IsLiveFullWait.decide c = true ↔ IsLiveFullWait c := by
  cases n with
  | zero =>
    have hc : c = 0 := by
      ext i
      exact Fin.elim0 i
    subst c
    have hwt : IsFullWait.Decidable.waitingTiles (Array.ofFn (0 : Hand 0)) = #[] := by
      rfl
    simp only [IsLiveFullWait.decide]
    rw [hwt]
    simp [IsLiveFullWait]
  | succ n =>
    simp only [IsLiveFullWait.decide, Bool.and_eq_true, Array.all_eq_true,
      Bool.or_eq_true, IsLiveFullWait]
    constructor
    · rintro ⟨⟨hsize, hwait⟩, hcount⟩
      have hcsize : Hand.size c = 3 * (n + 1) + 4 := by
        have hsize' := hsize.resolve_left (by simp)
        simpa using hsize'
      apply isLiveFullWait_iff_le_three.mpr
      refine ⟨?_, ?_⟩
      · intro i
        have hi := hwait i.val (by simp [IsFullWait.Decidable.waitingTiles_size])
        exact IsFullWait.Decidable.waitingTiles_spec c hcsize i |>.mp hi
      · intro i
        have hi := hcount i.val (by simp)
        simpa using hi
    · intro h
      rcases isLiveFullWait_iff_le_three.mp h with ⟨hfull, hcount⟩
      have hcsize := IsLiveFullWait.size (Nat.succ_pos n) h
      refine ⟨⟨Or.inr (by simpa using hcsize), ?_⟩, ?_⟩
      · intro i hi
        let j : Fin (3 * (n + 1)) := ⟨i, by
          simpa [IsFullWait.Decidable.waitingTiles_size] using hi⟩
        exact IsFullWait.Decidable.waitingTiles_spec c hcsize j |>.mpr (hfull j)
      · intro i hi
        have hi' := hcount ⟨i, by simpa using hi⟩
        simpa using hi'

instance (c : Hand n) : Decidable (IsLiveFullWait c) :=
  decidable_of_iff (IsLiveFullWait.decide c = true) (decide_spec c)

end IsLiveFullWait.Decidable

end Mahjong.Hand
