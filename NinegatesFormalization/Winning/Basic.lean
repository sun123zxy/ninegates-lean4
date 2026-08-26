import NinegatesFormalization.Meldable.Basic

/-!
# Winning hands and waits

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

lemma Winning.size {c : Hand n} (hc : Winning c) : size c = 3 * n + 5 := hc.2.1

end Mahjong.Hand
