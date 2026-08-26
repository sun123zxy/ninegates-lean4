import NinegatesFormalization.Winning.Basic
import NinegatesFormalization.Meldable.Decidable

namespace Mahjong.Hand.Winning.Scan

variable {n : ℕ}

/-- The finite state carried by the winning-hand dynamic program.

`prev₂` and `prev₁` are the numbers of canonical sequences started at the
preceding two coordinates.  Canonicalization makes both values smaller than
three; `pairUsed` records whether the pair has already been consumed. -/
@[ext, grind ext]
structure State where
  prev₂ : Fin 3
  prev₁ : Fin 3
  pairUsed : Bool
deriving DecidableEq, Fintype, Inhabited, Repr

/-- A local transition choice: consume a pair at this coordinate or not. -/
structure Choice where
  takePair : Bool
deriving DecidableEq, Fintype, Inhabited, Repr

@[inline]
def pairTiles (takePair : Bool) : ℕ :=
  if takePair then 2 else 0

@[inline]
def nextState (s : State) (takePair : Bool) (x : ℕ) : Option State :=
  if s.pairUsed && takePair then
    none
  else if s.prev₂.val + s.prev₁.val + pairTiles takePair ≤ x then
    let residual := x - (s.prev₂.val + s.prev₁.val + pairTiles takePair)
    some {
      prev₂ := s.prev₁
      prev₁ := ⟨residual % 3, Nat.mod_lt _ (by omega)⟩
      pairUsed := s.pairUsed || takePair
    }
  else
    none

def replayChoices : State → List ℕ → List Choice → Option State
  | s, [], [] => some s
  | s, x :: xs, choice :: choices => do
      let t ← nextState s choice.takePair x
      replayChoices t xs choices
  | _, _, _ => none

@[inline]
def insertState (t : State) (states : List State) : List State :=
  if t ∈ states then states else t :: states

@[simp]
lemma mem_insertState_iff (u t : State) (states : List State) :
    u ∈ insertState t states ↔ u = t ∨ u ∈ states := by
  unfold insertState
  split
  · rename_i ht
    constructor
    · exact Or.inr
    · rintro (rfl | hu)
      · exact ht
      · exact hu
  · simp

@[inline]
def oneState (states : List State) (s : State) (x : ℕ) : List State :=
  [false, true].foldl (fun next takePair ↦
    match nextState s takePair x with
    | none => next
    | some t => insertState t next) states

@[simp]
lemma mem_oneState_iff (u : State) (states : List State) (s : State) (x : ℕ) :
    u ∈ oneState states s x ↔
      u ∈ states ∨ nextState s false x = some u ∨ nextState s true x = some u := by
  cases h₀ : nextState s false x with
  | none =>
      cases h₁ : nextState s true x <;> simp [oneState, h₀, h₁] <;> grind
  | some t₀ =>
      cases h₁ : nextState s true x <;>
        (simp [oneState, h₀, h₁, or_comm, or_left_comm] <;> grind)

@[inline]
def oneTile (states : List State) (x : ℕ) : List State :=
  states.foldl (fun next s ↦ oneState next s x) []

@[inline, grind =]
def stateStep (s : State) (acc : List State) (x : ℕ) : List State :=
  let acc := match nextState s false x with
    | none => acc
    | some t => insertState t acc
  match nextState s true x with
  | none => acc
  | some t => insertState t acc

@[simp, grind =]
lemma stateStep_eq_oneState (s : State) (acc : List State) (x : ℕ) :
    stateStep s acc x = oneState acc s x := by
  simp [stateStep, oneState]

lemma mem_foldl_oneState_iff (u : State) (acc states : List State) (x : ℕ) :
    u ∈ states.foldl (fun next s ↦ oneState next s x) acc ↔
      u ∈ acc ∨ ∃ s ∈ states, u ∈ oneState [] s x := by
  induction states generalizing acc with
  | nil => simp
  | cons s states ih =>
      simp only [List.foldl]
      rw [ih]
      simp only [mem_oneState_iff]
      grind

lemma mem_oneTile_iff (u : State) (states : List State) (x : ℕ) :
    u ∈ oneTile states x ↔ ∃ s ∈ states, u ∈ oneState [] s x := by
  simpa [oneTile] using mem_foldl_oneState_iff u [] states x

@[inline]
def reachable : List State → List ℕ → List State
  | states, [] => states
  | states, x :: xs => reachable (oneTile states x) xs

lemma mem_reachable_iff (u : State) (states : List State) (xs : List ℕ) :
    u ∈ reachable states xs ↔
      ∃ s ∈ states, ∃ choices, replayChoices s xs choices = some u := by
  induction xs generalizing states with
  | nil =>
      change u ∈ states ↔ _
      constructor
      · intro h
        exact ⟨u, h, [], rfl⟩
      · rintro ⟨s, hs, choices, h⟩
        cases choices with
        | nil =>
            have : s = u := by simpa [replayChoices] using h
            simpa [this] using hs
        | cons choice choices => simp [replayChoices] at h
  | cons x xs ih =>
      rw [reachable, ih]
      constructor
      · rintro ⟨t, ht, choices, hrest⟩
        obtain ⟨s, hs, hstep⟩ := (mem_oneTile_iff t states x).mp ht
        obtain ⟨choice, hchoice⟩ :
            ∃ choice : Choice, nextState s choice.takePair x = some t := by
          rcases (mem_oneState_iff t [] s x).mp hstep with h | h
          · simp at h
          · rcases h with h | h
            · exact ⟨⟨false⟩, by simpa using h⟩
            · exact ⟨⟨true⟩, by simpa using h⟩
        exact ⟨s, hs, choice :: choices, by
          simp [replayChoices, hchoice, hrest]⟩
      · rintro ⟨s, hs, choices, hchoices⟩
        cases choices with
        | nil => simp [replayChoices] at hchoices
        | cons choice choices =>
            cases hnext : nextState s choice.takePair x with
            | none => simp [replayChoices, hnext] at hchoices
            | some t =>
                have hrest : replayChoices t xs choices = some u := by
                  simpa [replayChoices, hnext] using hchoices
                have hmem : t ∈ oneState [] s x := by
                  apply (mem_oneState_iff t [] s x).mpr
                  cases hpair : choice.takePair
                  · exact Or.inr (Or.inl (by simpa [hpair] using hnext))
                  · exact Or.inr (Or.inr (by simpa [hpair] using hnext))
                exact ⟨t, (mem_oneTile_iff t states x).mpr
                  ⟨s, hs, hmem⟩,
                  choices, hrest⟩

lemma foldl_oneTile_eq_reachable (states : List State) (xs : List ℕ) :
    xs.foldl (fun states x ↦ oneTile states x) states = reachable states xs := by
  induction xs generalizing states <;> simp [reachable, *]

def scanState (s : State) : Meldable.Scan.State := (s.prev₁.val, s.prev₂.val)

def adjustPair : List ℕ → List Choice → List ℕ
  | x :: xs, choice :: choices =>
      (x - pairTiles choice.takePair) :: adjustPair xs choices
  | _, _ => []

def handOfList (xs : List ℕ) (h : xs.length = 3 * n) : Hand n :=
  ⟨fun i ↦ xs.get ⟨i.val, by omega⟩⟩

lemma adjustPair_length {xs : List ℕ} {choices : List Choice}
    (h : choices.length = xs.length) : (adjustPair xs choices).length = xs.length := by
  induction xs generalizing choices with
  | nil => cases choices <;> simp [adjustPair] at h ⊢
  | cons x xs ih =>
      cases choices with
      | nil => simp at h
      | cons choice choices => simp [adjustPair, ih (by simpa using h)]

lemma adjustPair_get {xs : List ℕ} {choices : List Choice}
    (h : choices.length = xs.length) (i : Fin xs.length) :
    (adjustPair xs choices).get ⟨i.val, by simp [adjustPair_length h]⟩ =
      xs.get i - pairTiles (choices.get ⟨i.val, by omega⟩).takePair := by
  induction xs generalizing choices with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      cases choices with
      | nil => simp at h
      | cons choice choices =>
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp [adjustPair]
          · simpa [adjustPair] using ih (by simpa using h) j

lemma list_ofFn_handOfList (xs : List ℕ) (h : xs.length = 3 * n) :
    List.ofFn (handOfList xs h) = xs := by
  apply List.ext_getElem
  · simp [handOfList, h]
  · intro i hi₁ hi₂
    simp [handOfList, h]

lemma replayChoices_length {s t : State} {xs : List ℕ} {choices : List Choice}
    (h : replayChoices s xs choices = some t) : choices.length = xs.length := by
  induction xs generalizing s choices with
  | nil => cases choices <;> simp [replayChoices] at h ⊢
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons choice choices =>
          cases hnext : nextState s choice.takePair x with
          | none => simp [replayChoices, hnext] at h
          | some next =>
              have hrest : replayChoices next xs choices = some t := by
                simpa [replayChoices, hnext] using h
              simp [ih hrest]

lemma replayChoices_pair_index {s t : State} {xs : List ℕ} {choices : List Choice}
    (hlen : choices.length = xs.length)
    (h : replayChoices s xs choices = some t)
    (hs : s.pairUsed = false) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length,
      (choices.get i).takePair = true ∧
        2 ≤ xs.get ⟨i.val, by simpa [hlen] using i.isLt⟩ := by
  induction xs generalizing s choices with
  | nil =>
      cases choices <;> simp at hlen h ⊢
      cases h
      simp [hs] at ht
  | cons x xs ih =>
      cases choices with
      | nil => simp at hlen
      | cons choice choices =>
          cases hp : choice.takePair with
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hp, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hp, hn] using h
                  have hnext : next.pairUsed = false := by
                    simp [nextState, hs] at hn
                    grind
                  obtain ⟨i, hi, hxi⟩ := ih (by simpa using hlen) hrest hnext
                  refine ⟨Fin.succ i, ?_, ?_⟩
                  · simpa using hi
                  · simpa using hxi
          | true =>
              cases hn : nextState s true x with
              | none => simp [replayChoices, hp, hn] at h
              | some next =>
                  refine ⟨0, by simp [hp], ?_⟩
                  have hneed : s.prev₂.val + s.prev₁.val + 2 ≤ x := by
                    simp [nextState, hs, pairTiles] at hn
                    omega
                  change 2 ≤ x
                  omega

lemma nextState_to_scanStep (s t : State) (b : Bool) (x : ℕ)
    (h : nextState s b x = some t) :
    ∃ p : Meldable.StepPlacement,
      Meldable.Scan.step (scanState s) (x - pairTiles b) =
        some (p, scanState t) := by
  simp only [nextState] at h
  cases b with
  | false =>
      simp [pairTiles] at h
      rcases h with ⟨hneed, rfl⟩
      let residual := x - (s.prev₂.val + s.prev₁.val)
      refine ⟨⟨residual / 3, ⟨residual % 3, Nat.mod_lt _ (by omega)⟩⟩, ?_⟩
      have hneed' : s.prev₁.val + s.prev₂.val ≤ x := by omega
      have hsub : x - pairTiles false - (s.prev₁.val + s.prev₂.val) = residual := by
        simp [pairTiles, residual]
        omega
      have hcomm : s.prev₁.val + s.prev₂.val = s.prev₂.val + s.prev₁.val := by omega
      simp [Meldable.Scan.step, scanState, pairTiles, hneed, hneed', hsub, residual, hcomm]
  | true =>
      simp [pairTiles] at h
      rcases h with ⟨_, hneed, rfl⟩
      let residual := x - (s.prev₂.val + s.prev₁.val + 2)
      refine ⟨⟨residual / 3, ⟨residual % 3, Nat.mod_lt _ (by omega)⟩⟩, ?_⟩
      have hneed' : s.prev₁.val + s.prev₂.val ≤ x - 2 := by omega
      have hsub : x - 2 - (s.prev₁.val + s.prev₂.val) = residual := by
        simp [residual]
        omega
      simp [Meldable.Scan.step, scanState, pairTiles, hneed', hsub, residual]

lemma scanStep_to_nextState (s t : State) (p : Meldable.StepPlacement) (x : ℕ)
    (h : Meldable.Scan.step (scanState s) x = some (p, scanState t)) :
    nextState s false x = some { t with pairUsed := s.pairUsed } := by
  have hr := (Meldable.Scan.step_eq_some_iff_replay (scanState s) x p
    (scanState t)).mp h
  simp [Meldable.Scan.replay, scanState, nextState, pairTiles] at hr ⊢
  rcases hr with ⟨hx, hprev₁, hprev₂⟩
  refine ⟨by omega, Fin.ext hprev₂, ?_⟩
  apply Fin.ext
  have hsub : x - (s.prev₂.val + s.prev₁.val) = 3 * p.tripNum + p.seqNum.val := by
    omega
  simp [hsub, hprev₁]

lemma scanStep_to_nextState_pair (s t : State) (p : Meldable.StepPlacement) (x : ℕ)
    (hs : s.pairUsed = false)
    (h : Meldable.Scan.step (scanState s) x = some (p, scanState t)) :
    nextState s true (x + 2) = some { t with pairUsed := true } := by
  have hr := (Meldable.Scan.step_eq_some_iff_replay (scanState s) x p
    (scanState t)).mp h
  simp [Meldable.Scan.replay, scanState, nextState, pairTiles, hs] at hr ⊢
  rcases hr with ⟨hx, hprev₁, hprev₂⟩
  refine ⟨by omega, Fin.ext hprev₂, ?_⟩
  apply Fin.ext
  have hsub : x - (s.prev₂.val + s.prev₁.val) = 3 * p.tripNum + p.seqNum.val := by
    omega
  simp [hsub, hprev₁]

def advance (s : State) (p : Meldable.StepPlacement) : State :=
  ⟨s.prev₁, p.seqNum, s.pairUsed⟩

def traceState : State → List Meldable.StepPlacement → State
  | s, [] => s
  | s, p :: ps => traceState (advance s p) ps

def noPairChoices : List Meldable.StepPlacement → List Choice
  | [] => []
  | _ :: ps => ⟨false⟩ :: noPairChoices ps

def pairChoicesAt : List Meldable.StepPlacement → ℕ → List Choice
  | [], _ => []
  | _ :: ps, 0 => ⟨true⟩ :: noPairChoices ps
  | _ :: ps, k + 1 => ⟨false⟩ :: pairChoicesAt ps k

def addPairAt : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: xs, 0 => (x + 2) :: xs
  | x :: xs, k + 1 => x :: addPairAt xs k

@[simp]
lemma addPairAt_length (xs : List ℕ) (k : ℕ) : (addPairAt xs k).length = xs.length := by
  induction xs generalizing k with
  | nil => simp [addPairAt]
  | cons x xs ih => cases k <;> simp [addPairAt, ih]

lemma addPairAt_get (xs : List ℕ) (k : ℕ) (i : Fin xs.length) :
    (addPairAt xs k).get ⟨i.val, by simp⟩ =
      xs.get i + if i.val = k then 2 else 0 := by
  induction xs generalizing k with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · cases k <;> simp [addPairAt]
      · cases k with
        | zero => simp [addPairAt]
        | succ k => simpa [addPairAt] using ih k i

lemma list_ofFn_add_pair (d : Hand n) (i : Fin (3 * n)) :
    List.ofFn (d + pair i) = addPairAt (List.ofFn d) i.val := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    let jf : Fin (List.ofFn d).length := ⟨j, by simpa using hj₁⟩
    have hget := addPairAt_get (List.ofFn d) i.val jf
    simpa [jf, add_apply, pair_apply] using hget.symm

@[simp]
lemma scanState_advance (s : State) (p : Meldable.StepPlacement) :
    scanState (advance s p) = (Meldable.Scan.replay (scanState s) p).2 := by
  simp [scanState, advance, Meldable.Scan.replay]

@[simp]
lemma scanState_traceState (s : State) (ps : List Meldable.StepPlacement) :
    scanState (traceState s ps) = (Meldable.Scan.replayList (scanState s) ps).2 := by
  induction ps generalizing s with
  | nil => simp [traceState, Meldable.Scan.replayList]
  | cons p ps ih =>
      simp [traceState, Meldable.Scan.replayList, ih]

@[simp]
lemma traceState_pairUsed (s : State) (ps : List Meldable.StepPlacement) :
    (traceState s ps).pairUsed = s.pairUsed := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simpa [traceState, advance] using ih (advance s p)

@[simp]
lemma nextState_replay_false (s : State) (p : Meldable.StepPlacement) :
    nextState s false (Meldable.Scan.replay (scanState s) p).1 =
      some (advance s p) := by
  apply scanStep_to_nextState s (advance s p) p
  exact Meldable.Scan.step_replay (scanState s) p

@[simp]
lemma nextState_replay_true (s : State) (p : Meldable.StepPlacement)
    (hs : s.pairUsed = false) :
    nextState s true ((Meldable.Scan.replay (scanState s) p).1 + 2) =
      some (advance { s with pairUsed := true } p) := by
  apply scanStep_to_nextState_pair s (advance s p) p _ hs
  exact Meldable.Scan.step_replay (scanState s) p

lemma replayChoices_noPair_replayList (s : State) (ps : List Meldable.StepPlacement) :
    replayChoices s (Meldable.Scan.replayList (scanState s) ps).1
        (noPairChoices ps) = some (traceState s ps) := by
  induction ps generalizing s with
  | nil => simp [Meldable.Scan.replayList, noPairChoices, traceState, replayChoices]
  | cons p ps ih =>
      have hnext := nextState_replay_false s p
      simpa only [Meldable.Scan.replayList, noPairChoices, traceState, replayChoices,
        hnext, Option.bind_eq_bind, Option.bind_some, scanState_advance] using
        ih (advance s p)

lemma replayChoices_pair_replayList (s : State) (ps : List Meldable.StepPlacement)
    (k : ℕ) (hk : k < ps.length) (hs : s.pairUsed = false) :
    replayChoices s
        (addPairAt (Meldable.Scan.replayList (scanState s) ps).1 k)
        (pairChoicesAt ps k) =
      some (traceState { s with pairUsed := true } ps) := by
  induction ps generalizing s k with
  | nil => simp at hk
  | cons p ps ih =>
      cases k with
      | zero =>
          have hnext := nextState_replay_true s p hs
          simp only [Meldable.Scan.replayList, addPairAt, pairChoicesAt, replayChoices]
          rw [hnext]
          simp only [Option.bind_eq_bind, Option.bind_some]
          simpa [scanState, advance, traceState] using
            replayChoices_noPair_replayList (advance { s with pairUsed := true } p) ps
      | succ k =>
          have hk' : k < ps.length := by simpa using hk
          have hnext := nextState_replay_false s p
          simp only [Meldable.Scan.replayList, addPairAt, pairChoicesAt, replayChoices]
          rw [hnext]
          simp only [Option.bind_eq_bind, Option.bind_some]
          simpa [scanState, advance, traceState] using ih (s := advance s p) k hk' hs

lemma replayChoices_to_stepList {s t : State} {xs : List ℕ} {choices : List Choice}
    (h : replayChoices s xs choices = some t) :
    ∃ ps, Meldable.Scan.stepList (scanState s) (adjustPair xs choices) =
      some (ps, scanState t) := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil =>
          have : s = t := by simpa [replayChoices] using h
          subst t
          exact ⟨[], by simp [adjustPair, Meldable.Scan.stepList]⟩
      | cons choice choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons choice choices =>
          cases hnext : nextState s choice.takePair x with
          | none => simp [replayChoices, hnext] at h
          | some next =>
              have hrest : replayChoices next xs choices = some t := by
                simpa [replayChoices, hnext] using h
              obtain ⟨p, hp⟩ := nextState_to_scanStep s next choice.takePair x hnext
              obtain ⟨ps, hps⟩ := ih hrest
              refine ⟨p :: ps, ?_⟩
              simp [adjustPair, Meldable.Scan.stepList, hp, hps]

lemma replayChoices_pair_get_of_false {s : State} {xs : List ℕ} {choices : List Choice}
    {t : State} (hs : s.pairUsed = false)
    (h : replayChoices s xs choices = some t)
    (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length, (choices.get i).takePair = true := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil =>
          cases h
          have : t.pairUsed = false := by simpa using hs
          grind
      | cons choice choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons choice choices =>
          cases hp : choice.takePair with
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hp, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hp, hn] using h
                  have hnext : next.pairUsed = false := by
                    simp [nextState] at hn
                    grind
                  obtain ⟨i, hi⟩ := ih hnext hrest
                  exact ⟨Fin.succ i, by simpa using hi⟩
          | true =>
              exact ⟨0, by simp [hp]⟩

lemma replayChoices_pair_get {xs : List ℕ} {choices : List Choice} {t : State}
    (h : replayChoices ⟨0, 0, false⟩ xs choices = some t)
    (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length, (choices.get i).takePair = true :=
  replayChoices_pair_get_of_false rfl h ht

lemma replayChoices_all_false_of_true {s t : State} {xs : List ℕ} {choices : List Choice}
    (hs : s.pairUsed = true) (h : replayChoices s xs choices = some t) :
    ∀ i : Fin choices.length, (choices.get i).takePair = false := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil => intro i; exact Fin.elim0 i
      | cons choice choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons choice choices =>
          cases hp : choice.takePair with
          | true =>
              have hn : nextState s true x = none := by simp [nextState, hs]
              simp [replayChoices, hp, hn] at h
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hp, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hp, hn] using h
                  have hnext : next.pairUsed = true := by
                    simp [nextState, hs] at hn
                    grind
                  intro i
                  refine Fin.cases ?_ (fun j ↦ ?_) i
                  · simp [hp]
                  · simpa using ih hnext hrest j

lemma replayChoices_pair_unique_of_false {s t : State} {xs : List ℕ}
    {choices : List Choice} (hs : s.pairUsed = false)
    (h : replayChoices s xs choices = some t) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length, (choices.get i).takePair = true ∧
      ∀ j, j ≠ i → (choices.get j).takePair = false := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil =>
          cases h
          simp [hs] at ht
      | cons choice choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons choice choices =>
          cases hp : choice.takePair with
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hp, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hp, hn] using h
                  have hnext : next.pairUsed = false := by
                    simp [nextState, hs] at hn
                    grind
                  obtain ⟨i, hi, huniq⟩ := ih hnext hrest
                  refine ⟨Fin.succ i, by simpa using hi, ?_⟩
                  intro j
                  refine Fin.cases ?_ (fun j ↦ ?_) j
                  · intro _
                    simp [hp]
                  · intro hj
                    apply huniq
                    intro hEq
                    exact hj (by simpa using congrArg Fin.succ hEq)
          | true =>
              cases hn : nextState s true x with
              | none => simp [replayChoices, hp, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hp, hn] using h
                  have hnext : next.pairUsed = true := by
                    simp [nextState, hs] at hn
                    grind
                  have hfalse := replayChoices_all_false_of_true hnext hrest
                  refine ⟨0, by simp [hp], ?_⟩
                  intro j
                  refine Fin.cases ?_ (fun j ↦ ?_) j
                  · intro hj
                    exact False.elim (hj rfl)
                  · intro _
                    simpa using hfalse j

def DPWinning (c : Hand n) : Prop :=
  Valid c ∧ Hand.size c = 3 * n + 5 ∧
    ∃ choices, replayChoices ⟨0, 0, false⟩ (List.ofFn c) choices = some ⟨0, 0, true⟩

@[inline]
def WinCheck (c : Hand n) : Bool :=
  Id.run do
    if !decide (Valid c) then
      return false
    if !decide (Hand.size c = 3 * n + 5) then
      return false
    let mut states : List State := [⟨0, 0, false⟩]
    for x in List.ofFn c do
      let mut next : List State := []
      for s in states do
        next := stateStep s next x
      states := next
    return decide (⟨0, 0, true⟩ ∈ states)

lemma winCheck_spec (c : Hand n) :
    WinCheck c = true ↔ DPWinning c := by
  by_cases hv : Valid c
  · by_cases hs : Hand.size c = 3 * n + 5
    · simp [WinCheck, DPWinning, hv, hs, stateStep_eq_oneState]
      change _ ∈ (List.ofFn c).foldl (fun states x ↦ oneTile states x)
        [⟨0, 0, false⟩] ↔ _
      rw [foldl_oneTile_eq_reachable]
      simp [mem_reachable_iff]
    · simp [WinCheck, DPWinning, hv, hs]
  · simp [WinCheck, DPWinning, hv]

lemma dpWinning_to_winning {c : Hand n} (h : DPWinning c) : Winning c := by
  rcases h with ⟨hcvalid, hcsize, choices, hchoices⟩
  have hlen : choices.length = (List.ofFn c).length := replayChoices_length hchoices
  have hlen' : choices.length = 3 * n := by simpa using hlen
  obtain ⟨i, hi, huniq⟩ := replayChoices_pair_unique_of_false rfl hchoices rfl
  obtain ⟨i', hi', hxi'⟩ := replayChoices_pair_index hlen hchoices rfl rfl
  have hii : i' = i := by
    by_contra hne
    have hfalse := huniq i' hne
    rw [hi'] at hfalse
    cases hfalse
  have hi_x : i.val < (List.ofFn c).length := by simpa [hlen] using i.isLt
  have hxi : 2 ≤ (List.ofFn c).get ⟨i.val, hi_x⟩ := by
    simpa [hii] using hxi'
  let adjusted := adjustPair (List.ofFn c) choices
  have hadjusted : adjusted.length = 3 * n := by
    simp [adjusted, adjustPair_length hlen, hlen']
  let d : Hand n := handOfList adjusted hadjusted
  have hdlist : List.ofFn d = adjusted := list_ofFn_handOfList adjusted hadjusted
  obtain ⟨ps, hstep⟩ := replayChoices_to_stepList hchoices
  have hscan : Meldable.Scan.scan (List.ofFn d) = some ps := by
    rw [hdlist]
    exact (Meldable.Scan.scan_eq_some_iff_stepList _ _).mpr hstep
  have hdmeld : Meldable d := by
    rw [Meldable.iff_meldScan]
    have hne : Meldable.Scan.scan (List.ofFn d) ≠ none := by
      intro hnone
      rw [hscan] at hnone
      simp at hnone
    simp only [meldScan]
    split
    · exact (hne ‹_›).elim
    · simp
  have hi_lt : i.val < 3 * n := by omega
  let idx : Fin (3 * n) := ⟨i.val, hi_lt⟩
  have hcd : c = d + pair idx := by
    ext j
    have hj : j.val < (List.ofFn c).length := by simpa using j.isLt
    let ji : Fin choices.length := ⟨j.val, by simpa [hlen] using hj⟩
    let jx : Fin (List.ofFn c).length := ⟨j.val, hj⟩
    have hgetj : adjusted.get ⟨j.val, by simp [adjusted, adjustPair_length hlen]⟩ =
        (List.ofFn c).get jx - pairTiles (choices.get ji).takePair := by
      simpa [adjusted, ji, jx] using adjustPair_get hlen jx
    have hchoice : (choices.get ji).takePair =
        if j = idx then true else false := by
      by_cases hji : j = idx
      · subst j
        simpa [ji, idx] using hi
      · have hne : ji ≠ i := by
          intro heq
          apply hji
          apply Fin.ext
          simpa [idx] using congrArg Fin.val heq
        simp [hji]
        exact huniq ji hne
    have hbase : d j = (List.ofFn c).get jx - pairTiles (choices.get ji).takePair := by
      simpa [d, handOfList, jx, ji] using hgetj
    have hcx : (List.ofFn c).get jx = c j := by simp [jx]
    simp only [add_apply, pair_apply]
    by_cases hji : j = idx
    · subst j
      have hji_i : ji = i := by
        apply Fin.ext
        simp [ji, idx]
      have hxi'': 2 ≤ c idx := by simpa [idx] using hxi
      rw [hbase, hcx]
      rw [hji_i, hi]
      simp [pairTiles]
      omega
    · rw [hbase, hcx]
      rw [hchoice]
      simp [pairTiles, hji, Fin.ext_iff]
      omega
  exact ⟨hcvalid, hcsize, d, idx, hdmeld, hcd⟩

lemma winning_to_dpWinning {c : Hand n} (h : Winning c) : DPWinning c := by
  rcases h with ⟨hcvalid, hcsize, d, i, hdmeld, hcd⟩
  refine ⟨hcvalid, hcsize, ?_⟩
  obtain ⟨p, hp, hcanonical⟩ := (Meldable.iff_exists_canonical_witness d).mp hdmeld
  let ps := Meldable.Scan.disjoinCanonicalPlacement p hcanonical
  have hreplay := Meldable.Scan.replayList_disjoinCanonicalPlacement p hcanonical
  have hvalues : (Meldable.Scan.replayList (0, 0) ps).1 = List.ofFn d := by
    have := congrArg Prod.fst hreplay
    change p.toHand = d at hp
    rw [hp] at this
    simpa [ps] using this
  have hfinal : (Meldable.Scan.replayList (0, 0) ps).2 = (0, 0) := by
    have := congrArg Prod.snd hreplay
    simpa [ps] using this
  have hk : i.val < ps.length := by
    simp [ps, Meldable.Scan.disjoinCanonicalPlacement]
  let initial : State := ⟨0, 0, false⟩
  have hrun := replayChoices_pair_replayList initial ps i.val hk rfl
  have hinput :
      addPairAt (Meldable.Scan.replayList (scanState initial) ps).1 i.val =
        List.ofFn c := by
    rw [show scanState initial = (0, 0) by rfl, hvalues]
    rw [← list_ofFn_add_pair d i, hcd]
  have hstate : traceState { initial with pairUsed := true } ps = ⟨0, 0, true⟩ := by
    have hscan : scanState (traceState { initial with pairUsed := true } ps) =
        (0, 0) := by
      rw [scanState_traceState]
      simpa [initial, scanState] using hfinal
    have hpair := traceState_pairUsed { initial with pairUsed := true } ps
    apply State.ext <;> simp [scanState, initial] at hscan hpair ⊢ <;> grind
  refine ⟨pairChoicesAt ps i.val, ?_⟩
  rw [hinput, hstate] at hrun
  exact hrun

theorem winCheck_correct {c : Hand n} : WinCheck c = true ↔ Winning c := by
  rw [winCheck_spec]
  exact ⟨dpWinning_to_winning, winning_to_dpWinning⟩

instance (c : Hand n) : Decidable (Winning c) :=
  decidable_of_iff (WinCheck c = true) winCheck_correct

end Mahjong.Hand.Winning.Scan
