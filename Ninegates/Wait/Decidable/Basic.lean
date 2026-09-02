import Ninegates.Wait.Basic
import Ninegates.Winning.Decidable

/-!
# Decidability of waits and full waits, the trivial version

As efficient algorithms for deciding winning is established in `Winning.Decidable`,
we can trivially decide waits and full waits by checking all possible tiles.

The new definitions `WaitingTiles` and `LiveWaitingTiles` are `Finset` versions of waiting tiles.
It is defined here as `Finset` requires a decidable predicate.
Note that you should use `IsWaitingTile c i ` in general
if you only need to check whether a specific tile is a waiting tile.
This `Finset` version is mainly designed for computational purposes.

Note that now it is still an $O(n^2)$ trivial algorithm.
The efficient $O(n)$ algorithms are implemented in `Algo` and proved correct in `AlgoSpec`.
The verified Finset implementations are registered with `@[csimp]` there, making `#eval
waitingTiles` and `#eval liveWaitingTiles` run in $O(n)$ time.

For `IsWait`, `IsLiveWait`, `IsFullWait`, and `IsLiveFullWait`,
we choose to retain the trivial $O(n^2)$ algorithms here,
as they

- will short-circuit in the sreach for a (non)-waiting tile.
- the $O(n)$ algorithm requires building prefix/suffix state sets,
  an overhead that can be expensive for small `n`.
-/

namespace Mahjong.Hand

variable {n : ℕ}

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsWaitingTile c i) := by
  unfold IsWaitingTile
  infer_instance

instance (c : Hand n) (i : Fin (3 * n)) : Decidable (IsLiveWaitingTile c i) := by
  unfold IsLiveWaitingTile
  infer_instance

def waitingTiles (c : Hand n) : Finset (Fin (3 * n)) :=
  {i | IsWaitingTile c i}

def liveWaitingTiles (c : Hand n) : Finset (Fin (3 * n)) :=
  {i | IsLiveWaitingTile c i}

instance (c : Hand n) : Decidable (IsWait c) := by
  unfold IsWait
  infer_instance

instance (c : Hand n) : Decidable (IsLiveWait c) := by
  unfold IsLiveWait
  infer_instance

instance (c : Hand n) : Decidable (IsFullWait c) := by
  unfold IsFullWait
  infer_instance

instance (c : Hand n) : Decidable (IsLiveFullWait c) := by
  unfold IsLiveFullWait
  infer_instance

end Mahjong.Hand
