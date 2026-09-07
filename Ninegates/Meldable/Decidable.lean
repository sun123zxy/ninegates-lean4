import Ninegates.Meldable.Canonical

/-!
# Verified scanning algorithm for meld decompositions

## Main definitions

- `State` records the two sequence counts still requiring the current tile.
- `StepPlacement` records the triplets and sequences selected at one coordinate.
- `step` processes one tile count, failing when the pending sequences cannot be met.
- `replay` reconstructs the previous (count, state) from the current (step placement, state).
- `stepList` and `replayList` extend these operations to lists.
- `scanList` scans a list from left to right and rejects unfinished sequences at the end.
- `scanHand` scans a hand and returns its canonical placement on success.

## Main results

- `scanHand_sound`: a successful scan returns a canonical witness for the input hand.
- `scanHand_toHand`: scanning the hand of a placement returns its canonicalization.
- `scanHand_iff_meldable`: Hand meldability by successful scanning.
- Meldability is efficiently `Decidable` by scanning.

## Execution

`scanHand` is executable! Try `#eval scanHand (.triplet 0 : Hand 3)` for example.

## Design notes

### Program verification

Unlike the winning and waiting checking algorithms,
we delibrately mixed the meldability algorithm and its correctness proof in a single module.
This is because the partial function `step` and the total function `replay`
are almost inverses of each other. With this symmetry,
the algorithm is simple enough to be verified alongside its implementation.
-/

namespace Mahjong.Hand

namespace Meldable.Decidable

/-- The melds selected by the scan at one coordinate. -/
@[ext, grind ext]
structure StepPlacement where
  tripNum : ℕ
  seqNum : Fin 3
deriving DecidableEq, Inhabited, Repr

/-- The sequence counts from the previous two coordinates that require the current tile. -/
abbrev State := ℕ × ℕ

/-- Process one tile count and update the pending sequence counts. -/
@[grind =]
def step (state : State) (x : ℕ) : Option (StepPlacement × State) :=
  if state.1 + state.2 ≤ x then
    let residual := x - (state.1 + state.2)
    let p : StepPlacement :=
      ⟨residual / 3, ⟨residual % 3, Nat.mod_lt _ (by omega)⟩⟩
    some (p, (p.seqNum.val, state.1))
  else none

/-- Reconstruct the previous (count, state) from the current (step placement, state). -/
@[grind =]
def replay (state : State) (p : StepPlacement) : ℕ × State :=
  (state.1 + state.2 + 3 * p.tripNum + p.seqNum.val,
   (p.seqNum.val, state.1))

@[simp, grind =]
lemma replay_fst (state : State) (p : StepPlacement) :
    (replay state p).1 =
      state.1 + state.2 + 3 * p.tripNum + p.seqNum.val := rfl

@[simp, grind =]
lemma replay_snd (state : State) (p : StepPlacement) :
    (replay state p).2 = (p.seqNum.val, state.1) := rfl

@[simp, grind =]
lemma step_replay (state : State) (p : StepPlacement) :
    step state (replay state p).1 = some (p, (replay state p).2) := by
  grind [step, replay]

lemma step_eq_some_iff_replay (state : State) (x : ℕ)
    (p : StepPlacement) (next : State) :
    step state x = some (p, next) ↔ replay state p = (x, next) := by
  grind [step, replay]

/-- Scan a list of tile counts, retaining the final pending state. -/
def stepList : State → List ℕ → Option (List StepPlacement × State)
  | state, [] => some ([], state)
  | state, x :: xs => do
      let (p, next) ← step state x
      let (ps, final) ← stepList next xs
      some (p :: ps, final)

/-- Reconstruct tile counts and the final state from a list of step placements. -/
def replayList : State → List StepPlacement → List ℕ × State
  | state, [] => ([], state)
  | state, p :: ps =>
      let (x, next) := replay state p
      let (xs, final) := replayList next ps
      (x :: xs, final)

@[simp, grind =]
lemma stepList_cons_eq_some_cons_iff (state : State) (x : ℕ) (xs : List ℕ)
    (p : StepPlacement) (ps : List StepPlacement) (final : State) :
    stepList state (x :: xs) = some (p :: ps, final) ↔
      ∃ next, step state x = some (p, next) ∧
        stepList next xs = some (ps, final) := by
  simp [stepList, Option.bind_eq_some_iff]

@[simp]
lemma stepList_cons_ne_some_nil (state : State) (x : ℕ) (xs : List ℕ)
    (final : State) : stepList state (x :: xs) ≠ some ([], final) := by
  simp [stepList, Option.bind_eq_some_iff]

theorem stepList_eq_some_iff_replayList (state : State) (xs : List ℕ)
    (ps : List StepPlacement) (final : State) :
    stepList state xs = some (ps, final) ↔ replayList state ps = (xs, final) := by
  induction xs generalizing state ps final with
  | nil => cases ps <;> simp [stepList, replayList]
  | cons x xs ih =>
      cases ps with
      | nil => simp [replayList]
      | cons p ps =>
          simp [replayList, step_eq_some_iff_replay, ih]
          grind

@[simp, grind =]
lemma stepList_replayList (state : State) (ps : List StepPlacement) :
    stepList state (replayList state ps).1 = some (ps, (replayList state ps).2) :=
  (stepList_eq_some_iff_replayList _ _ _ _).mpr rfl

/-- Scan tile counts from left to right and return their coordinate placements. -/
def scanList (xs : List ℕ) : Option (List StepPlacement) := do
  let (ps, final) ← stepList (0, 0) xs
  if final = (0, 0) then some ps else none

@[simp, grind =]
lemma scanList_eq_some_iff_stepList (xs : List ℕ) (ps : List StepPlacement) :
    scanList xs = some ps ↔ stepList (0, 0) xs = some (ps, (0, 0)) := by
  change (stepList (0, 0) xs).bind (fun result =>
    if result.2 = (0, 0) then some result.1 else none) = some ps ↔ _
  rw [Option.bind_eq_some_iff]
  grind

theorem scanList_eq_some_iff (xs : List ℕ) (ps : List StepPlacement) :
    scanList xs = some ps ↔ replayList (0, 0) ps = (xs, (0, 0)) := by
  rw [scanList_eq_some_iff_stepList, stepList_eq_some_iff_replayList]

@[simp, grind =]
lemma replayList_length (state : State) (ps : List StepPlacement) :
    (replayList state ps).1.length = ps.length := by
  induction ps generalizing state with
  | nil => rfl
  | cons p ps ih => simp [replayList, ih]

lemma replayList_snd_of_length_ge_two (state : State) (ps : List StepPlacement)
    (hlength : 2 ≤ ps.length) : (replayList state ps).2 =
      ((ps.get ⟨ps.length - 1, by omega⟩).seqNum.val,
        (ps.get ⟨ps.length - 2, by omega⟩).seqNum.val) := by
  induction ps generalizing state with
  | nil => simp at hlength
  | cons p ps ih =>
      cases ps with
      | nil => simp at hlength
      | cons q qs =>
          cases qs with
          | nil => simp [replayList]
          | cons r rs => grind [replayList]

@[grind →]
lemma replayList_of_scanList {xs : List ℕ} {ps : List StepPlacement}
    (h : scanList xs = some ps) : replayList (0, 0) ps = (xs, (0, 0)) :=
  (scanList_eq_some_iff xs ps).mp h

lemma exists_scanList_of_replayList {xs : List ℕ}
    (h : ∃ ps, replayList (0, 0) ps = (xs, (0, 0))) :
    ∃ ps, scanList xs = some ps := by
  obtain ⟨ps, hps⟩ := h
  exact ⟨ps, (scanList_eq_some_iff xs ps).mpr hps⟩

@[grind →]
lemma length_of_scanList {xs : List ℕ} {ps : List StepPlacement}
    (h : scanList xs = some ps) : ps.length = xs.length := by grind

lemma seqNum_tail_eq_zero_of_replayList (state : State) (ps : List StepPlacement)
    (hlength : 2 ≤ ps.length) (hfinal : (replayList state ps).2 = (0, 0)) :
    (ps.get ⟨ps.length - 2, by omega⟩).seqNum.val = 0 ∧
      (ps.get ⟨ps.length - 1, by omega⟩).seqNum.val = 0 := by
  grind [replayList_snd_of_length_ge_two state ps hlength]

lemma replayList_get (state : State) (ps : List StepPlacement) (i : Fin ps.length) :
    (replayList state ps).1.get ⟨i.val, by simp [replayList_length]⟩ =
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
      · simp [replayList]
      · cases ps with
        | nil => exact Fin.elim0 i
        | cons q qs =>
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · have h := ih (state := (p.seqNum.val, state.1)) ⟨0, by simp⟩
              simp [replayList] at h ⊢
            · have h := ih (state := (p.seqNum.val, state.1)) (Fin.succ j)
              simp [replayList] at h ⊢
              grind

/-- Split a canonical placement into the coordinate choices consumed by `scanList`. -/
def disjoinCanonicalPlacement (p : Placement n) (hp : p.Canonical) : List StepPlacement :=
  List.ofFn fun i ↦ ⟨p.tripNum i, ⟨p.seqNum i, hp i⟩⟩

lemma replayList_disjoinCanonicalPlacement (p : Placement n) (hp : p.Canonical) :
    replayList (0, 0) (disjoinCanonicalPlacement p hp) =
      (List.ofFn p.toHand, (0, 0)) := by
  by_cases hn : n = 0
  · subst n
    simp [disjoinCanonicalPlacement, replayList]
  apply Prod.ext
  · apply List.ext_getElem
    · simp [replayList_length, disjoinCanonicalPlacement]
    · intro k hk₁ hk₂
      have hk : k < (disjoinCanonicalPlacement p hp).length := by
        simpa [replayList_length] using hk₁
      have hcoord := replayList_get (0, 0) (disjoinCanonicalPlacement p hp) ⟨k, hk⟩
      grind [disjoinCanonicalPlacement]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have htail :=
      replayList_snd_of_length_ge_two (0, 0) (disjoinCanonicalPlacement p hp)
        (by simp [disjoinCanonicalPlacement]; omega)
    grind [disjoinCanonicalPlacement]

variable {n : ℕ} {c : Hand n} {ps : List StepPlacement}

/-- Join the step placements from a successful scan into the corresponding placement. -/
def joinStepPlacements
    (h : scanList (List.ofFn c) = some ps) : Placement n :=
  have hlength : ps.length = 3 * n := by simpa using length_of_scanList h
  ⟨(fun i ↦ (ps.get ⟨i.val, by omega⟩).tripNum),
    (fun i ↦ (ps.get ⟨i.val, by omega⟩).seqNum.val), by
      by_cases hn : n = 0
      · grind
      have hfinal : (replayList (0, 0) ps).2 = (0, 0) := by
        exact congrArg Prod.snd (replayList_of_scanList h)
      have hzero := seqNum_tail_eq_zero_of_replayList (0, 0) ps (by omega) hfinal
      grind⟩

/-- The placement joined from a successful scan is canonical. -/
lemma joinStepPlacements_canonical
    (h : scanList (List.ofFn c) = some ps) :
    (joinStepPlacements h).Canonical := by
  intro i
  simp [joinStepPlacements]

lemma disjoinCanonicalPlacement_joinStepPlacements
    (h : scanList (List.ofFn c) = some ps) :
    disjoinCanonicalPlacement (joinStepPlacements h) (joinStepPlacements_canonical h) = ps := by
  apply List.ext_getElem
  · simp [disjoinCanonicalPlacement, length_of_scanList h]
  · intro i hi₁ hi₂
    simp [disjoinCanonicalPlacement, joinStepPlacements]

/-- The placement joined from a successful scan gives the scanned hand. -/
theorem joinStepPlacements_isWitness
    (h : scanList (List.ofFn c) = some ps) :
    IsWitness (joinStepPlacements h) c := by
  simp only [IsWitness]
  have hreplay :=
    replayList_disjoinCanonicalPlacement (joinStepPlacements h) (joinStepPlacements_canonical h)
  rw [disjoinCanonicalPlacement_joinStepPlacements h] at hreplay
  have hlists := congrArg Prod.fst (hreplay.symm.trans (replayList_of_scanList h))
  ext i
  exact congrFun (List.ofFn_injective hlists) i

variable {n : ℕ}

/-- Scan a hand and return its canonical meld placement when the scan succeeds. -/
def scanHand (c : Hand n) : Option (Meldable.Placement n) :=
  match h : scanList (List.ofFn c) with
  | none => none
  | some _ => some (joinStepPlacements h)

/-- A successful scan returns a canonical witness for the input hand. -/
theorem scanHand_sound {c : Hand n} {p : Meldable.Placement n}
    (h : scanHand c = some p) :
    Meldable.IsWitness p c ∧ p.Canonical := by
  simp only [scanHand] at h
  split at h
  · contradiction
  · cases h
    exact ⟨joinStepPlacements_isWitness _, joinStepPlacements_canonical _⟩

/-- Scanning the hand given by a placement returns its canonicalization. -/
theorem scanHand_toHand (p : Meldable.Placement n) :
    scanHand p.toHand = some p.canonicalize := by
  let q := p.canonicalize
  have hq : q.Canonical := Meldable.Placement.Canonical.canonicalize p
  have hreplay :
      replayList (0, 0) (disjoinCanonicalPlacement q hq) =
        (List.ofFn p.toHand, (0, 0)) := by
    simpa [q] using replayList_disjoinCanonicalPlacement q hq
  obtain ⟨ps, hscan⟩ :=exists_scanList_of_replayList ⟨_, hreplay⟩
  have hresult : scanHand p.toHand = some (joinStepPlacements hscan) := by
    grind [scanHand]
  have hsound := scanHand_sound hresult
  have hplacement : joinStepPlacements hscan = q := by
    apply Meldable.Placement.Canonical.unique hsound.2 hq
    simp only [Meldable.IsWitness] at hsound
    simpa [q] using hsound.1
  simpa [q, hplacement] using hresult

/-- A hand is meldable exactly when scanning it succeeds. -/
theorem scanHand_iff_meldable (c : Hand n) : Meldable c ↔ (scanHand c).isSome := by
  constructor
  · rintro ⟨p, rfl⟩
    exact Option.isSome_iff_exists.2 ⟨p.canonicalize, scanHand_toHand p⟩
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
    exact ⟨p, (scanHand_sound hp).1⟩

instance (c : Hand n) : Decidable (Meldable c) :=
  decidable_of_iff (scanHand c).isSome (scanHand_iff_meldable c).symm

end Mahjong.Hand.Meldable.Decidable
