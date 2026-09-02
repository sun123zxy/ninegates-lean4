import Ninegates.Winning.Basic

/-!
## Wait predicates

* `IsWaitingTile c i` tests whether adding tile `i` has a winning decomposition.
* `IsLiveWaitingTile c i` additionally requires the resulting hand to be valid.
* `IsWait` and `IsFullWait` allow dead tiles, while their `IsLive...` counterparts do not.
-/

namespace Mahjong.Hand

variable {n : ℕ}

def IsWaitingTile (c : Hand n) (i : Fin (3 * n)) : Prop := Winning (c + single i)

def IsLiveWaitingTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  IsWaitingTile c i ∧ Valid (c + single i)

lemma isLiveWaitingTile_iff {c : Hand n} {i : Fin (3 * n)} :
    IsLiveWaitingTile c i ↔ IsWaitingTile c i ∧ Valid c ∧ c i ≤ 3 := by
  simp [IsLiveWaitingTile, IsWaitingTile, Valid]
  grind

def IsWait (c : Hand n) : Prop := ∃ i, IsWaitingTile c i

lemma IsWait.size {c : Hand n} (hc : IsWait c) : size c = 3 * n + 4 := by
  obtain ⟨i, hi⟩ := hc
  have hsize := hi.size
  rw [map_add, size_single] at hsize
  omega

def IsLiveWait (c : Hand n) : Prop := ∃ i, IsLiveWaitingTile c i

lemma IsWait.toIsLiveWait {c : Hand n} (hc : IsWait c)
    (hvalid : ∀ i, IsWaitingTile c i → Valid (c + single i)) :
    IsLiveWait c := by
  obtain ⟨i, hi⟩ := hc
  exact ⟨i, hi, hvalid i hi⟩

lemma IsLiveWait.size {c : Hand n} (hc : IsLiveWait c) : size c = 3 * n + 4 := by
  obtain ⟨i, hi⟩ := hc
  exact IsWait.size ⟨i, hi.1⟩

lemma IsLiveWait.valid (c : Hand n) (hc : IsLiveWait c) : Valid c := by
  obtain ⟨w, ⟨_, hwvalid⟩⟩ := hc
  intro i
  have hi := hwvalid i
  simp only [add_apply] at hi
  omega

def IsFullWait (c : Hand n) : Prop := ∀ i, IsWaitingTile c i

def IsLiveFullWait (c : Hand n) : Prop := ∀ i, IsLiveWaitingTile c i

lemma IsFullWait.toIsLiveFullWait {c : Hand n} (hc : IsFullWait c)
    (hvalid : ∀ i, Valid (c + single i)) : IsLiveFullWait c := by
  intro i
  exact ⟨hc i, hvalid i⟩

lemma isLiveFullWait_iff_le_three {c : Hand n} :
    IsLiveFullWait c ↔ IsFullWait c ∧ ∀ i, c i ≤ 3 := by
  simp only [IsLiveFullWait, IsFullWait, isLiveWaitingTile_iff]
  grind

lemma IsFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    size c = 3 * n + 4 := by
  let i : Fin (3 * n) := ⟨0, by omega⟩
  exact IsWait.size ⟨i, hc i⟩

lemma IsLiveFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsLiveFullWait c) :
    size c = 3 * n + 4 :=
  let i : Fin (3 * n) := ⟨0, by omega⟩
  IsLiveWait.size ⟨i, hc i⟩

lemma IsLiveFullWait.le_three {c : Hand n} (hc : IsLiveFullWait c) : ∀ i, c i ≤ 3 := by
  exact isLiveFullWait_iff_le_three.mp hc |>.2

end Mahjong.Hand
