import NinegatesFormalization.Meldable.Canonical
import Std.Internal.Do
import Std.Tactic.Do

/-!
# Verified scanning algorithm for meld decompositions

## Main Definitions

- `Scan.State` records the two sequence counts still requiring the current tile.
- `Scan.StepPlacement` records the triplets and sequences selected at one coordinate.
- `Scan.step` processes one tile count, failing when the pending sequences cannot be met.
- `Scan.scan` scans a list from left to right and rejects unfinished sequences at the end.
- `Hand.meldScan` scans a hand and returns its canonical placement on success.

`Scan.replay` reconstructs tile counts from step placements. It is the semantic inverse of
scanning: at each coordinate it adds the two pending sequence counts, three copies of every
triplet, and the newly started sequences. The verification of `Scan.scan` uses `replay` both
as its loop invariant and as its final specification.

## Main Results

- A successful scan returns a canonical witness for the input hand.
- Scanning the hand of a placement returns its canonicalization.
- A hand is `Meldable` exactly when its scan succeeds.
-/

namespace Mahjong.Hand.Meldable.Scan

open Std.Internal.Do

/-- The sequence counts from the previous two coordinates that require the current tile. -/
abbrev State := ℕ × ℕ

/-- The melds selected by the scan at one coordinate. -/
@[ext, grind ext]
structure StepPlacement where
  tripNum : ℕ
  seqNum : Fin 3
deriving DecidableEq, Inhabited, Repr

/-- Process one tile count and update the pending sequence counts. -/
def step (state : State) (x : ℕ) : Option (StepPlacement × State) :=
  if state.1 + state.2 ≤ x then
    let residual := x - (state.1 + state.2)
    let p : StepPlacement :=
      ⟨residual / 3, ⟨residual % 3, Nat.mod_lt _ (by omega)⟩⟩
    some (p, (p.seqNum.val, state.1))
  else
    none

/--
Reconstruct the tile counts described by step placements, starting with a pending state.

At each coordinate, a placement contributes three tiles for every triplet and one tile for
every newly started sequence, in addition to the two pending sequence counts. The resulting
state carries the newly started sequences and the first component of the previous state.

This is the semantic inverse of `scan`. Its equation on the already scanned prefix is the
loop invariant used by `vcgen`, and its equation on the complete input is the scan postcondition.
-/
def replay : State → List StepPlacement → List ℕ × State
  | state, [] => ([], state)
  | state, p :: ps =>
      let x := state.1 + state.2 + 3 * p.tripNum + p.seqNum.val
      let (xs, final) := replay (p.seqNum.val, state.1) ps
      (x :: xs, final)

/-- Scan tile counts from left to right and return their coordinate placements. -/
def scan (xs : List ℕ) : Option (List StepPlacement) := do
  let mut state : State := (0, 0)
  let mut revPlacements : List StepPlacement := []
  for x in xs do
    let (p, next) ← step state x
    state := next
    revPlacements := p :: revPlacements
  if state = (0, 0) then
    some revPlacements.reverse
  else
    none

@[spec]
lemma step_spec (state : State) (x : ℕ) :
    ⦃ True ⦄ (m := Option)
      step state x
    ⦃ (fun result ↦
        state.1 + state.2 ≤ x ∧
          replay state [result.1] = ([x], result.2));
      ¬state.1 + state.2 ≤ x ⦄ := by
  sorry

/--
The `vcgen` specification of the scanning loop. Its invariant says that replaying the
reversed accumulator reconstructs exactly the prefix visited by the list cursor and reaches
the current pending state.
-/
@[spec]
lemma scan_spec (xs : List ℕ) :
    ⦃ True ⦄ (m := Option)
      scan xs
    ⦃ (fun ps ↦ replay (0, 0) ps = (xs, (0, 0)));
      ¬∃ ps, replay (0, 0) ps = (xs, (0, 0)) ⦄ := by
  sorry

lemma replay_length (state : State) (ps : List StepPlacement) :
    (replay state ps).1.length = ps.length := by
  induction ps generalizing state with
  | nil => rfl
  | cons p ps ih => simp [replay, ih]

lemma length_of_scan {xs : List ℕ} {ps : List StepPlacement}
    (h : scan xs = some ps) : ps.length = xs.length := by
  have hreplay : replay (0, 0) ps = (xs, (0, 0)) :=
    Option.of_wp_eq h
      (fun
        | some ps => replay (0, 0) ps = (xs, (0, 0))
        | none => ¬∃ ps, replay (0, 0) ps = (xs, (0, 0)))
      ((scan_spec xs).le_wp trivial)
  have := congrArg (fun r : List ℕ × State ↦ r.1.length) hreplay
  simpa only [replay_length] using this

variable {n : ℕ} {c : Hand n} {ps : List StepPlacement}

/-- Turn a successful scan of a hand into the corresponding placement. -/
def toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) : Placement n :=
  have hlength : ps.length = 3 * n := by simpa using length_of_scan h
  ⟨(fun i ↦ (ps.get ⟨i.val, by omega⟩).tripNum),
    (fun i ↦ (ps.get ⟨i.val, by omega⟩).seqNum.val), by
      sorry⟩

/-- The placement extracted from a successful scan gives the scanned hand. -/
theorem isWitness_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    IsWitness (toPlacement h) c := by
  sorry

/-- The placement extracted from a successful scan is canonical. -/
lemma canonical_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    (toPlacement h).Canonical := by
  sorry

end Mahjong.Hand.Meldable.Scan

namespace Mahjong.Hand

variable {n : ℕ}

/-- Scan a hand and return its canonical meld placement when the scan succeeds. -/
def meldScan (c : Hand n) : Option (Meldable.Placement n) :=
  match h : Meldable.Scan.scan (List.ofFn fun i ↦ c i) with
  | none => none
  | some _ => some (Meldable.Scan.toPlacement h)

/-- A successful scan returns a canonical witness for the input hand. -/
theorem meldScan_sound {c : Hand n} {p : Meldable.Placement n}
    (h : c.meldScan = some p) :
    Meldable.IsWitness p c ∧ p.Canonical := by
  sorry

/-- Scanning the hand given by a placement returns its canonicalization. -/
theorem meldScan_toHand (p : Meldable.Placement n) :
    p.toHand.meldScan = some p.canonicalize := by
  sorry

/-- A hand is meldable exactly when scanning it succeeds. -/
theorem Meldable.iff_meldScan (c : Hand n) : Meldable c ↔ c.meldScan.isSome := by
  sorry

end Mahjong.Hand
