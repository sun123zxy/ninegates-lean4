import NinegatesFormalization.Meldable.Canonical
import Std.Tactic.Do

/-!
# Verified scanning algorithm for meld decompositions

## Main Definitions

- Before scanning coordinate `i`, a scan state `(a, b)` records the numbers of
  sequences started at `i - 1` and `i - 2` that require a tile at `i`.

- A scan step first supplies the tiles required by those sequences.  It fails if
  there are not enough tiles.  The remaining tiles form as many triplets as
  possible, and the remainder starts zero, one, or two new sequences.

- `scan` applies these steps from left to right and succeeds if the final state is
  `(0, 0)`.  It is implemented in `EStateM` and verified with
  `Std.Internal.Do.vcgen`.

- `Scan.Accepts c` means that scanning `c` succeeds.

## Main Results

- A hand is accepted by the scan if and only if it is `Meldable`.
- The choices made by an accepting scan give the canonical witness for the hand.
-/
