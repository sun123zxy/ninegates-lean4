import NinegatesFormalization.Meldable.Canonical

/-!
# Verified scanning algorithm for meld decompositions

## Main Definitions

- `Scan.State` records the two sequence counts still requiring the current tile.
- `Meldable.StepPlacement` records the triplets and sequences selected at one coordinate.
- `Scan.step` processes one tile count, failing when the pending sequences cannot be met.
- `Scan.replay` reconstructs the previous (count, state) from the current (step placement, state).
- `Scan.stepList` and `Scan.replayList` extend these operations to lists.
- `Scan.scan` scans a list from left to right and rejects unfinished sequences at the end.
- `Hand.meldScan` scans a hand and returns its canonical placement on success.

Note that the partial function `step` and the total function `replay`
are almost inverses of each other. With this symmetry,
we can prove correctness of the scan algorithm swiftly without using `vcgen`,
which might be a little boilerplate-heavy for this simple algorithm.

## Main Results

- A successful scan returns a canonical witness for the input hand.
- Scanning the hand of a placement returns its canonicalization.
- A hand is `Meldable` exactly when its scan succeeds.
-/

namespace Mahjong.Hand.Meldable

/-- The melds selected by the scan at one coordinate. -/
@[ext, grind ext]
structure StepPlacement where
  tripNum : ℕ
  seqNum : Fin 3
deriving DecidableEq, Inhabited, Repr

namespace Scan

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
def scan (xs : List ℕ) : Option (List StepPlacement) := do
  let (ps, final) ← stepList (0, 0) xs
  if final = (0, 0) then some ps else none

@[simp, grind =]
lemma scan_eq_some_iff_stepList (xs : List ℕ) (ps : List StepPlacement) :
    scan xs = some ps ↔ stepList (0, 0) xs = some (ps, (0, 0)) := by
  change (stepList (0, 0) xs).bind (fun result =>
    if result.2 = (0, 0) then some result.1 else none) = some ps ↔ _
  rw [Option.bind_eq_some_iff]
  grind

theorem scan_eq_some_iff (xs : List ℕ) (ps : List StepPlacement) :
    scan xs = some ps ↔ replayList (0, 0) ps = (xs, (0, 0)) := by
  rw [scan_eq_some_iff_stepList, stepList_eq_some_iff_replayList]

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
lemma replayList_of_scan {xs : List ℕ} {ps : List StepPlacement}
    (h : scan xs = some ps) : replayList (0, 0) ps = (xs, (0, 0)) :=
  (scan_eq_some_iff xs ps).mp h

lemma exists_scan_of_replayList {xs : List ℕ}
    (h : ∃ ps, replayList (0, 0) ps = (xs, (0, 0))) :
    ∃ ps, scan xs = some ps := by
  obtain ⟨ps, hps⟩ := h
  exact ⟨ps, (scan_eq_some_iff xs ps).mpr hps⟩

@[grind →]
lemma length_of_scan {xs : List ℕ} {ps : List StepPlacement}
    (h : scan xs = some ps) : ps.length = xs.length := by grind

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

end Scan

/-- Encode a canonical placement as the coordinate choices consumed by `Scan.scan`. -/
def Placement.toStepPlacements (p : Placement n) (hp : p.Canonical) : List StepPlacement :=
  List.ofFn fun i ↦ ⟨p.tripNum i, ⟨p.seqNum i, hp i⟩⟩

lemma Scan.toStepPlacements_replayList (p : Placement n) (hp : p.Canonical) :
    Scan.replayList (0, 0) (p.toStepPlacements hp) =
      (List.ofFn (fun i ↦ p.toHand i), (0, 0)) := by
  by_cases hn : n = 0
  · subst n
    simp [Placement.toStepPlacements, Scan.replayList]
  apply Prod.ext
  · apply List.ext_getElem
    · simp [Scan.replayList_length, Placement.toStepPlacements]
    · intro k hk₁ hk₂
      have hk : k < (p.toStepPlacements hp).length := by
        simpa [Scan.replayList_length] using hk₁
      have hcoord :=
        Scan.replayList_get (0, 0) (p.toStepPlacements hp) ⟨k, hk⟩
      simp [Placement.toStepPlacements] at hcoord ⊢
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
    have htail :=
      Scan.replayList_snd_of_length_ge_two (0, 0) (p.toStepPlacements hp)
        (by simp [Placement.toStepPlacements]; omega)
    simp [Placement.toStepPlacements] at htail ⊢
    grind [p.seqNum_tail]

namespace Scan

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
      have hfinal : (replayList (0, 0) ps).2 = (0, 0) := by
        exact congrArg Prod.snd (replayList_of_scan h)
      have hzero :=
        seqNum_tail_eq_zero_of_replayList (0, 0) ps (by omega) hfinal
      constructor <;> intro i hi <;> grind⟩

/-- The placement extracted from a successful scan is canonical. -/
lemma canonical_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    (toPlacement h).Canonical := by
  intro i
  simp [toPlacement]

lemma toStepPlacements_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    Placement.toStepPlacements (toPlacement h) (canonical_toPlacement h) = ps := by
  apply List.ext_getElem
  · simp [Placement.toStepPlacements, length_of_scan h]
  · intro i hi₁ hi₂
    simp [Placement.toStepPlacements, toPlacement]

/-- The placement extracted from a successful scan gives the scanned hand. -/
theorem isWitness_toPlacement
    (h : scan (List.ofFn fun i ↦ c i) = some ps) :
    IsWitness (toPlacement h) c := by
  simp only [IsWitness]
  have hreplay :=
    Scan.toStepPlacements_replayList (toPlacement h) (canonical_toPlacement h)
  rw [toStepPlacements_toPlacement h] at hreplay
  have hlists :=
    congrArg Prod.fst (hreplay.symm.trans (replayList_of_scan h))
  ext i
  exact congrFun (List.ofFn_injective hlists) i

end Scan
end Mahjong.Hand.Meldable

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
      Meldable.Scan.replayList (0, 0) (Meldable.Placement.toStepPlacements q hq) =
        (List.ofFn (fun i ↦ p.toHand i), (0, 0)) := by
    simpa [q] using Meldable.Scan.toStepPlacements_replayList q hq
  obtain ⟨ps, hscan⟩ := Meldable.Scan.exists_scan_of_replayList ⟨_, hreplay⟩
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
