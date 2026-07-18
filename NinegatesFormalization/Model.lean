import Mathlib

namespace Mahjong

abbrev Hand (n : ℕ) := Fin (3 * n) → ℕ

variable {n : ℕ}

abbrev TripletAt (i : Fin (3 * n)) : Hand n :=
  fun j ↦ if j = i then 3 else 0

abbrev SequenceAt (i : Fin (3 * n - 2)) : Hand n :=
  fun (j : Fin (3 * n)) ↦
    if j.val = i.val ∨ j.val = i.val + 1 ∨ j.val = i.val + 2 then 1 else 0

abbrev PairAt (i : Fin (3 * n)) : Hand n :=
  fun j ↦ if j = i then 2 else 0

namespace Hand

def Valid (c : Hand n) : Prop := ∀ i, c i ≤ 4

def Meldable (c : Hand n) : Prop :=
  ∃ (t : Fin (3 * n) → ℕ) (r : Fin (3 * n - 2) → ℕ),
  c = ∑ i, t i • TripletAt i + ∑ j, r j • SequenceAt j

@[simp]
lemma Meldable.sequenceAt {i : Fin (3 * n - 2)} : Meldable (SequenceAt i) := by
  use 0, fun j ↦ if j = i then 1 else 0
  simp

@[simp]
lemma Meldable.tripletAt {i : Fin (3 * n)} : Meldable (TripletAt i) := by
  use fun j ↦ if j = i then 1 else 0, 0
  simp

@[simp]
lemma Meldable.add (c d : Hand n) (hc : Meldable c) (hd : Meldable d) : Meldable (c + d) := by
  obtain ⟨tc, rc, hc⟩ := hc
  obtain ⟨td, rd, hd⟩ := hd
  use tc + td, rc + rd
  rw [hc, hd]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  ring

def Winning (c : Hand n) : Prop :=
  Valid c ∧ ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + PairAt i

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop :=
  Winning (c + PairAt i)

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + PairAt i)

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + PairAt i)

def standardFullWait : Hand n :=
  fun i ↦ if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1

end Hand

end Mahjong
