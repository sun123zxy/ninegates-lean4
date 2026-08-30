import Ninegates.Winning.Basic

/-!
## Wait predicates

* `IsWinningTile c i` tests whether adding tile `i` has a winning decomposition.
* `IsLiveWinningTile c i` additionally requires the resulting hand to be valid.
* `IsWait` and `IsFullWait` allow dead tiles, while their `IsLive...` counterparts do not.
-/

namespace Mahjong.Hand

variable {n : ℕ}

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop := Winning (c + single i)

def IsLiveWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  IsWinningTile c i ∧ Valid (c + single i)

def IsWait (c : Hand n) : Prop := ∃ i, IsWinningTile c i

lemma IsWait.size {c : Hand n} (hc : IsWait c) : size c = 3 * n + 4 := by
  obtain ⟨i, hi⟩ := hc
  have hsize := hi.size
  rw [map_add, size_single] at hsize
  omega

def IsLiveWait (c : Hand n) : Prop := ∃ i, IsLiveWinningTile c i

lemma IsWait.toIsLiveWait {c : Hand n} (hc : IsWait c)
    (hvalid : ∀ i, IsWinningTile c i → Valid (c + single i)) :
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

def IsFullWait (c : Hand n) : Prop := ∀ i, IsWinningTile c i

def IsLiveFullWait (c : Hand n) : Prop := ∀ i, IsLiveWinningTile c i

lemma IsFullWait.toIsLiveFullWait {c : Hand n} (hc : IsFullWait c)
    (hvalid : ∀ i, Valid (c + single i)) : IsLiveFullWait c := by
  intro i
  exact ⟨hc i, hvalid i⟩

lemma IsFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    size c = 3 * n + 4 := by
  let i : Fin (3 * n) := ⟨0, by omega⟩
  exact IsWait.size ⟨i, hc i⟩

lemma IsLiveFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsLiveFullWait c) :
    size c = 3 * n + 4 :=
  let i : Fin (3 * n) := ⟨0, by omega⟩
  IsLiveWait.size ⟨i, hc i⟩

lemma IsLiveFullWait.le_three {c : Hand n} (hc : IsLiveFullWait c) : ∀ i, c i ≤ 3 := by
  intro i
  have hi := (hc i).2 i
  grind

end Mahjong.Hand
