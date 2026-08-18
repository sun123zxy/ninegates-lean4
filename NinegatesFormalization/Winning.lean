import NinegatesFormalization.Meldable.Basic

/-!
# Winning hands and waits

## Winning hands

A `Winning c` hand is valid, has `3 * n + 5` tiles, and can be written as a meldable
hand plus one pair.  This separates the existential choice of the pair from the meld
decomposition developed in `Meldable.Basic`.

## Wait predicates

* `IsWinningTile c i` tests whether adding tile `i` wins.
* `IsWait c` asks for at least one winning tile.
* `IsFullWait c` requires every tile value to win.

The elementary results expose the forced hand sizes used by the positivity, standard
full-wait, and uniqueness arguments.
-/

namespace Mahjong.Hand

variable {n : ℕ}

def Winning (c : Hand n) : Prop :=
  Valid c ∧ size c = 3 * n + 5 ∧
    ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + pair i

@[grind →]
lemma Winning.size {c : Hand n} (hc : Winning c) : size c = 3 * n + 5 := hc.2.1

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop := Winning (c + single i)

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + single i)

@[grind →]
lemma IsWait.Valid (c : Hand n) (hc : IsWait c) : Valid c := by
  grind [IsWait, Winning, Valid]

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + single i)

@[grind →]
lemma IsFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    size c = 3 * n + 4 := by
  let i : Fin (3 * n) := ⟨0, by omega⟩
  have hsize := (hc i).size
  grind

end Mahjong.Hand
