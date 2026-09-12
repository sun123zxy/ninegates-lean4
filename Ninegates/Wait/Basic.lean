/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Wait.Defs
public import Ninegates.Winning.Basic

/-!
# Basic properties of waits
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

lemma isLiveWaitingTile_iff {c : Hand n} {i : Fin (3 * n)} :
    IsLiveWaitingTile c i ↔ IsWaitingTile c i ∧ Valid c ∧ c i ≤ 3 := by
  simp [IsLiveWaitingTile, IsWaitingTile, Valid]
  grind

lemma IsWait.size {c : Hand n} (hc : IsWait c) : size c = 3 * n + 4 := by
  obtain ⟨i, hi⟩ := hc
  have hsize := hi.size
  rw [map_add, size_single] at hsize
  omega

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

theorem IsFullWait.reverse {c : Hand n} (hc : IsFullWait c) : IsFullWait (reverse c) := by
  intro i
  change Winning (Hand.reverse c + single i)
  simpa only [map_add, reverse_single, Fin.rev_rev] using (hc i.rev).reverse

end Mahjong.Hand
