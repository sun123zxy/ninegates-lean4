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
@[grind =]
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

@[simp, grind =]
lemma replay_append (state : State) (ps qs : List StepPlacement) :
    replay state (ps ++ qs) =
      ((replay state ps).1 ++ (replay (replay state ps).2 qs).1,
        (replay (replay state ps).2 qs).2) := by
  induction ps generalizing state with
  | nil => rfl
  | cons p ps ih => simp [replay, ih]

/-- Scan tile counts from left to right and return their coordinate placements. -/
def scan (xs : List ℕ) : Option (List StepPlacement) := do
  let mut state : State := (0, 0)
  let mut revPlacements : List StepPlacement := []
  for x in xs do
    let (p, next) ← step state x
    state := next
    revPlacements := p :: revPlacements
  unless state = (0, 0) do
    throw ()
  return revPlacements.reverse

@[spec]
lemma step_spec (state : State) (x : ℕ) :
    ⦃ True ⦄ (m := Option)
      step state x
    ⦃ (fun result ↦
        state.1 + state.2 ≤ x ∧
          replay state [result.1] = ([x], result.2));
      ¬state.1 + state.2 ≤ x ⦄ := by
  refine ⟨?_⟩
  intro
  simp only [wp, WP.wpTrans]
  simp [step, replay]
  split <;> simp_all
  all_goals omega

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
  vcgen [scan] invariants
  | inv1 => fun cursor acc ↦
      replay (0, 0) acc.2.reverse = (cursor.prefix, acc.1) ∧
        ∀ ps, replay (0, 0) ps = (xs, (0, 0)) →
          ∃ qs, ps = acc.2.reverse ++ qs ∧
            replay acc.1 qs = (cursor.suffix, (0, 0))
  case vc1 => simp [replay]
  case vc2 acc hacc hzero => simpa [hzero] using hacc.1
  case vc3 acc hacc hzero =>
    rintro ⟨ps, hps⟩
    obtain ⟨qs, _, hqs⟩ := hacc.2 ps hps
    cases qs with
    | nil =>
        simp only [replay, Prod.mk.injEq, true_and] at hqs
        exact hzero hqs
    | cons q qs =>
        simp only [replay, Prod.mk.injEq, reduceCtorEq, false_and] at hqs
  case vc4 pref x suff hxs acc hacc hstep =>
    rintro ⟨ps, hps⟩
    obtain ⟨qs, _, hqs⟩ := hacc.2 ps hps
    cases qs <;> simp [replay] at hqs
    omega
  case vc5 pref x suff hxs acc hacc result hstep =>
    simp only [List.reverse_cons]
    constructor
    · rw [replay_append, hacc.1, hstep.2]
    · intro ps hps
      obtain ⟨qs, hfactor, hqs⟩ := hacc.2 ps hps
      cases qs with
      | nil => simp [replay] at hqs
      | cons q qs =>
          have hqcount :
              acc.1.1 + acc.1.2 + 3 * q.tripNum + q.seqNum.val = x := by
            simpa [replay] using
              congrArg (fun r : List ℕ × State ↦ r.1.head?) hqs
          have hresultcount :
              acc.1.1 + acc.1.2 + 3 * result.1.tripNum +
                result.1.seqNum.val = x := by
            simpa [replay] using
              congrArg (fun r : List ℕ × State ↦ r.1.head?) hstep.2
          have hpq : result.1 = q := by
            ext <;> omega
          subst q
          refine ⟨qs, by simpa [List.append_assoc] using hfactor, ?_⟩
          have hnext :
              (result.1.seqNum.val, acc.1.1) = result.2 := by
            simpa [replay] using congrArg Prod.snd hstep.2
          have htail :
              replay (result.1.seqNum.val, acc.1.1) qs =
                (suff, (0, 0)) := by
            apply Prod.ext
            · have hpair :
                  acc.1.1 + acc.1.2 + 3 * result.1.tripNum +
                      result.1.seqNum.val = x ∧
                    (replay (result.1.seqNum.val, acc.1.1) qs).1 = suff := by
                  simpa [replay] using congrArg Prod.fst hqs
              exact hpair.2
            · simpa [replay] using congrArg Prod.snd hqs
          rw [← hnext]
          exact htail

@[simp, grind =]
lemma replay_length (state : State) (ps : List StepPlacement) :
    (replay state ps).1.length = ps.length := by
  induction ps generalizing state with
  | nil => rfl
  | cons p ps ih => simp [replay, ih]

lemma replay_snd_of_length_ge_two (state : State) (ps : List StepPlacement)
    (hlength : 2 ≤ ps.length) :
    (replay state ps).2 =
      ((ps.get ⟨ps.length - 1, by omega⟩).seqNum.val,
        (ps.get ⟨ps.length - 2, by omega⟩).seqNum.val) := by
  induction ps generalizing state with
  | nil => simp at hlength
  | cons p ps ih =>
      cases ps with
      | nil => simp at hlength
      | cons q qs =>
          cases qs with
          | nil => simp [replay]
          | cons r rs =>
              simpa [replay] using
                ih (state := (p.seqNum.val, state.1)) (by simp)

@[grind →]
lemma replay_of_scan {xs : List ℕ} {ps : List StepPlacement}
    (h : scan xs = some ps) : replay (0, 0) ps = (xs, (0, 0)) :=
  Option.of_wp_eq h
    (fun
      | some ps => replay (0, 0) ps = (xs, (0, 0))
      | none => ¬∃ ps, replay (0, 0) ps = (xs, (0, 0)))
    ((scan_spec xs).le_wp trivial)

lemma exists_scan_of_replay {xs : List ℕ}
    (h : ∃ ps, replay (0, 0) ps = (xs, (0, 0))) :
    ∃ ps, scan xs = some ps := by
  cases hscan : scan xs with
  | none =>
      have hfail : ¬∃ ps, replay (0, 0) ps = (xs, (0, 0)) :=
        Option.of_wp_eq hscan
          (fun
            | some ps => replay (0, 0) ps = (xs, (0, 0))
            | none => ¬∃ ps, replay (0, 0) ps = (xs, (0, 0)))
          ((scan_spec xs).le_wp trivial)
      exact (hfail h).elim
  | some ps => exact ⟨ps, rfl⟩

@[grind →]
lemma length_of_scan {xs : List ℕ} {ps : List StepPlacement}
    (h : scan xs = some ps) : ps.length = xs.length := by
  have := congrArg (fun r : List ℕ × State ↦ r.1.length) (replay_of_scan h)
  simpa only [replay_length] using this

lemma seqNum_tail_eq_zero_of_replay (state : State) (ps : List StepPlacement)
    (hlength : 2 ≤ ps.length) (hfinal : (replay state ps).2 = (0, 0)) :
    (ps.get ⟨ps.length - 2, by omega⟩).seqNum.val = 0 ∧
      (ps.get ⟨ps.length - 1, by omega⟩).seqNum.val = 0 := by
  rw [replay_snd_of_length_ge_two state ps hlength] at hfinal
  exact ⟨congrArg Prod.snd hfinal, congrArg Prod.fst hfinal⟩

lemma replay_get (state : State) (ps : List StepPlacement) (i : Fin ps.length) :
    (replay state ps).1.get ⟨i.val, by simp [replay_length]⟩ =
      if i.val = 0 then
        state.1 + state.2 + 3 * (ps.get i).tripNum + (ps.get i).seqNum.val
      else if i.val = 1 then
        (ps.get ⟨0, by have := i.isLt; omega⟩).seqNum.val + state.1 +
          3 * (ps.get i).tripNum + (ps.get i).seqNum.val
      else
        (ps.get ⟨i.val - 1, by have := i.isLt; omega⟩).seqNum.val +
          (ps.get ⟨i.val - 2, by have := i.isLt; omega⟩).seqNum.val +
          3 * (ps.get i).tripNum + (ps.get i).seqNum.val := by
  induction ps generalizing state with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp [replay]
      · cases ps with
        | nil => exact Fin.elim0 i
        | cons q qs =>
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · have h := ih (state := (p.seqNum.val, state.1)) ⟨0, by simp⟩
              simp [replay] at h ⊢
            · have h := ih (state := (p.seqNum.val, state.1)) (Fin.succ j)
              simp [replay] at h ⊢
              by_cases hj : j.val = 0
              · simp_all
              · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
                simpa [hk] using h

/-- Encode a canonical placement as the coordinate choices consumed by `scan`. -/
def steps (p : Placement n) (hp : p.Canonical) : List StepPlacement :=
  List.ofFn fun i ↦ ⟨p.tripNum i, ⟨p.seqNum i, hp i⟩⟩

lemma replay_steps (p : Placement n) (hp : p.Canonical) :
    replay (0, 0) (steps p hp) =
      (List.ofFn (fun i ↦ p.toHand i), (0, 0)) := by
  by_cases hn : n = 0
  · subst n
    simp [steps, replay]
  apply Prod.ext
  · apply List.ext_getElem
    · simp [replay_length, steps]
    · intro k hk₁ hk₂
      have hk : k < (steps p hp).length := by
        simpa [replay_length] using hk₁
      have hcoord := replay_get (0, 0) (steps p hp) ⟨k, hk⟩
      simp [steps] at hcoord ⊢
      by_cases hk₀ : k = 0
      · simp [Placement.toHand_apply_of_eq_zero, hk₀] at ⊢ hcoord
        grind
      by_cases hk₁ : k = 1
      · simp [Placement.toHand_apply_of_eq_one, hk₁] at ⊢ hcoord
        grind
      · have hk₂ : 2 ≤ k := by omega
        simp [Placement.toHand_apply_of_ge_two, hk₂] at ⊢ hcoord
        grind
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have htail := replay_snd_of_length_ge_two (0, 0) (steps p hp) (by simp [steps]; omega)
    simp [steps] at htail ⊢
    grind [p.seqNum_tail]

variable {n : ℕ} {c : Hand n} {ps : List StepPlacement}

/-- Turn a successful scan of a hand into the corresponding placement. -/
def toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) : Placement n :=
  have hlength : ps.length = 3 * n := by simpa using length_of_scan h
  ⟨(fun i ↦ (ps.get ⟨i.val, by omega⟩).tripNum),
    (fun i ↦ (ps.get ⟨i.val, by omega⟩).seqNum.val), by
      by_cases hn : n = 0
      · subst n
        constructor <;> intro i <;> exact Fin.elim0 i
      have hfinal : (replay (0, 0) ps).2 = (0, 0) := by
        exact congrArg Prod.snd (replay_of_scan h)
      have hzero := seqNum_tail_eq_zero_of_replay (0, 0) ps (by omega) hfinal
      constructor
      · intro i hi
        have hindex :
            (⟨i.val, by omega⟩ : Fin ps.length) = ⟨ps.length - 2, by omega⟩ := by
          grind
        simpa only [hindex] using hzero.1
      · intro i hi
        have hindex :
            (⟨i.val, by omega⟩ : Fin ps.length) = ⟨ps.length - 1, by omega⟩ := by
          grind
        simpa only [hindex] using hzero.2⟩

/-- The placement extracted from a successful scan gives the scanned hand. -/
theorem isWitness_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    IsWitness (toPlacement h) c := by
  simp only [IsWitness]
  ext i
  have hlength : ps.length = 3 * n := by simpa using length_of_scan h
  have hcoord := replay_get (0, 0) ps ⟨i.val, by omega⟩
  have hvalue :
      (replay (0, 0) ps).1.get
          ⟨i.val, by simp [replay_length, hlength]⟩ = c i := by
    apply Option.some.inj
    have hi : i.val < (replay (0, 0) ps).1.length := by
      simp [replay_length, hlength]
    change some ((replay (0, 0) ps).1[i.val]'hi) = some (c i)
    rw [← List.getElem?_eq_getElem hi]
    rw [congrArg Prod.fst (replay_of_scan h)]
    simp
  have hcoord' := hvalue.symm.trans (by simpa using hcoord)
  by_cases hi₀ : i.val = 0
  · simp [Placement.toHand_apply_of_eq_zero, hi₀, toPlacement] at ⊢ hcoord'
    grind
  by_cases hi₁ : i.val = 1
  · simp [Placement.toHand_apply_of_eq_one, hi₁, toPlacement] at ⊢ hcoord'
    grind
  · have hi₂ : 2 ≤ i.val := by omega
    simp [Placement.toHand_apply_of_ge_two, hi₂, toPlacement] at ⊢ hcoord'
    grind

/-- The placement extracted from a successful scan is canonical. -/
lemma canonical_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    (toPlacement h).Canonical := by
  intro i
  simp [toPlacement]

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
  simp only [meldScan] at h
  split at h
  · contradiction
  · cases h
    exact ⟨Meldable.Scan.isWitness_toPlacement _,
      Meldable.Scan.canonical_toPlacement _⟩

/-- Scanning the hand given by a placement returns its canonicalization. -/
theorem meldScan_toHand (p : Meldable.Placement n) :
    p.toHand.meldScan = some p.canonicalize := by
  let q := p.canonicalize
  have hq : q.Canonical := Meldable.Placement.Canonical.canonicalize p
  have hreplay :
      Meldable.Scan.replay (0, 0) (Meldable.Scan.steps q hq) =
        (List.ofFn (fun i ↦ p.toHand i), (0, 0)) := by
    simpa [q] using Meldable.Scan.replay_steps q hq
  obtain ⟨ps, hscan⟩ := Meldable.Scan.exists_scan_of_replay ⟨_, hreplay⟩
  have hresult :
      p.toHand.meldScan = some (Meldable.Scan.toPlacement hscan) := by
    unfold meldScan
    split <;> grind
  have hsound := meldScan_sound hresult
  have hplacement : Meldable.Scan.toPlacement hscan = q := by
    apply Meldable.Placement.Canonical.unique hsound.2 hq
    simp only [Meldable.IsWitness] at hsound
    simpa [q] using hsound.1
  simpa [q, hplacement] using hresult

/-- A hand is meldable exactly when scanning it succeeds. -/
theorem Meldable.iff_meldScan (c : Hand n) : Meldable c ↔ c.meldScan.isSome := by
  constructor
  · rintro ⟨p, hp⟩
    simp only [Meldable.IsWitness] at hp
    rw [← hp]
    exact Option.isSome_iff_exists.2 ⟨p.canonicalize, meldScan_toHand p⟩
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
    exact ⟨p, (meldScan_sound hp).1⟩

end Mahjong.Hand
