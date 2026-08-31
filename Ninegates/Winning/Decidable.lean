import Ninegates.Winning.Decide
import Std.Data.ExtHashSet.Lemmas
import Ninegates.Meldable.Decidable

/-!
# Correctness of the winning-hand decision procedure
-/

namespace Mahjong.Hand.Winning.Decidable

variable {n : ℕ}

@[grind =]
def pairTiles (takePair : Bool) : ℕ :=
  if takePair then 2 else 0

def nextState (s : State) (takePair : Bool) (x : ℕ) : Option State :=
  if s.pairUsed && takePair then
    none
  else if s.a.val + s.b.val + pairTiles takePair ≤ x then
    let residual := x - (s.a.val + s.b.val + pairTiles takePair)
    some {
      a := ⟨residual % 3, by omega⟩
      b := s.a
      pairUsed := s.pairUsed || takePair
    }
  else
    none

def choice (x : ℕ) (s : State) (takePair : Bool) : StateSet :=
  match nextState s takePair x with
  | none => ∅
  | some t => (∅ : StateSet).insert t

@[grind =]
lemma step_eq_union (x : Nat) (s : State) :
    step x s = choice x s false ∪ choice x s true := by
  apply Std.ExtHashSet.ext_mem
  intro t
  simp [step, choice, nextState, pairTiles, emptyStateSet]
  grind

@[simp, grind =]
lemma mem_choice (x : Nat) (s t : State) (takePair : Bool) :
    t ∈ choice x s takePair ↔
      nextState s takePair x = some t := by
  cases h : nextState s takePair x <;> simp [choice, h]

@[simp, grind =]
lemma mem_step (x : Nat) (s t : State) :
    t ∈ step x s ↔
      nextState s false x = some t ∨ nextState s true x = some t := by
  simp [step_eq_union]

@[grind →]
lemma mem_step_of_nextState {x : Nat} {s t : State} {takePair : Bool}
    (h : nextState s takePair x = some t) : t ∈ step x s := by
  cases takePair <;> simp [h]

@[grind →]
lemma exists_nextState_of_mem_step {x : Nat} {s t : State}
    (h : t ∈ step x s) : ∃ takePair, nextState s takePair x = some t := by
  grind

@[grind →]
lemma nextState_pairUsed {s t : State} {takePair : Bool} {x : Nat}
    (h : nextState s takePair x = some t) :
    t.pairUsed = (s.pairUsed || takePair) := by
  simp [nextState] at h
  grind

@[grind →]
lemma nextState_need {s t : State} {takePair : Bool} {x : Nat}
    (h : nextState s takePair x = some t) :
    s.a.val + s.b.val + pairTiles takePair ≤ x := by
  simp [nextState] at h
  grind

lemma state_all (s : State) : s ∈ State.all := by
  rcases s with ⟨a, b, p⟩
  cases p <;> simp [State.all]

lemma mem_fold_union (xs : List State) (f : State → StateSet) (acc : StateSet) (t : State) :
    t ∈ xs.foldl (fun r q ↦ r ∪ f q) acc ↔
      t ∈ acc ∨ ∃ q ∈ xs, t ∈ f q := by
  induction xs generalizing acc <;>
    simp_all only [List.foldl, Std.ExtHashSet.mem_union_iff, List.mem_cons] <;> grind

lemma mem_fold_step (xs : List State) (x : Nat) (states : StateSet)
    (acc : StateSet) (t : State) :
    t ∈ xs.foldl
        (fun result q =>
          if states.contains q then result ∪ (step x q) else result)
        acc ↔
      t ∈ acc ∨ ∃ q ∈ xs, states.contains q ∧ t ∈ step x q := by
  induction xs generalizing acc with
  | nil => simp
  | cons q qs ih =>
      simp only [List.foldl]
      rw [ih]
      split <;> (simp_all <;> grind)

@[grind =]
lemma mem_stepSet (x : Nat) (states : StateSet) (t : State) :
    t ∈ stepSet x states ↔
      ∃ q : State, q ∈ states ∧ t ∈ step x q := by
  unfold stepSet
  rw [mem_fold_step]
  simp [emptyStateSet, Std.ExtHashSet.emptyWithCapacity_eq, state_all]

def replayChoices : State → List Nat → List Bool → Option State
  | s, [], [] => some s
  | s, x :: xs, takePair :: choices => do
      let t ← nextState s takePair x
      replayChoices t xs choices
  | _, _, _ => none

@[simp, grind =]
lemma replayChoices_cons_iff (s t : State) (x : Nat) (xs : List Nat)
    (takePair : Bool) (choices : List Bool) :
    replayChoices s (x :: xs) (takePair :: choices) = some t ↔
      ∃ u, nextState s takePair x = some u ∧ replayChoices u xs choices = some t := by
  cases h : nextState s takePair x <;> simp [replayChoices, h]

@[simp]
lemma replayChoices_exists_nil_iff (s t : State) :
    (∃ choices, replayChoices s [] choices = some t) ↔ s = t := by
  constructor
  · rintro ⟨choices, h⟩
    cases choices with
    | nil => simpa [replayChoices] using h
    | cons takePair choices => simp [replayChoices] at h
  · rintro rfl
    exact ⟨[], rfl⟩

grind_pattern replayChoices_exists_nil_iff => replayChoices s [] _, some t

@[simp]
lemma replayChoices_exists_cons_iff (s t : State) (x : Nat) (xs : List Nat) :
    (∃ choices, replayChoices s (x :: xs) choices = some t) ↔
      ∃ u, u ∈ step x s ∧ ∃ choices, replayChoices u xs choices = some t := by
  constructor
  · rintro ⟨choices, h⟩
    cases choices with
    | nil => simp [replayChoices] at h
    | cons takePair choices =>
        obtain ⟨u, hn, hr⟩ := (replayChoices_cons_iff s t x xs takePair choices).mp h
        exact ⟨u, mem_step_of_nextState hn, choices, hr⟩
  · rintro ⟨u, hu, choices, h⟩
    obtain ⟨takePair, hn⟩ := exists_nextState_of_mem_step hu
    exact ⟨takePair :: choices, by
      apply (replayChoices_cons_iff s t x xs takePair choices).mpr
      exact ⟨u, hn, h⟩⟩

grind_pattern replayChoices_exists_cons_iff => replayChoices s (x :: xs) _, some t

@[grind →]
lemma replayChoices_length {s t : State} {xs : List Nat} {choices : List Bool}
    (h : replayChoices s xs choices = some t) : choices.length = xs.length := by
  induction xs generalizing s choices with
  | nil => cases choices <;> simp [replayChoices] at h ⊢
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons takePair choices => grind

def reachable : StateSet → List Nat → StateSet
  | states, [] => states
  | states, x :: xs => reachable (stepSet x states) xs

@[grind =]
lemma mem_reachable (states : StateSet) (xs : List Nat) (t : State) :
    t ∈ reachable states xs ↔
      ∃ s, s ∈ states ∧
        ∃ choices, replayChoices s xs choices = some t := by
  induction xs generalizing states with
  | nil =>
      simp only [reachable, replayChoices_exists_nil_iff]
      grind
  | cons x xs ih =>
      rw [reachable, ih]
      simp only [mem_stepSet, replayChoices_exists_cons_iff]
      grind

lemma loop_reachable_from (states : StateSet) (xs : List Nat) :
    Id.run (do
      let mut current : StateSet := states
      for x in xs do
        current := stepSet x current
      return current) = reachable states xs := by
  induction xs generalizing states with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.forIn_cons, Id.run_bind]
      simpa [reachable] using (ih (states := stepSet x states))

lemma loop_reachable (xs : List Nat) :
    Id.run (do
      let mut states : StateSet := (∅ : StateSet).insert State.init
      for x in xs do
        states := stepSet x states
      return states) = reachable ((∅ : StateSet).insert State.init) xs := by
  simpa using loop_reachable_from ((∅ : StateSet).insert State.init) xs

lemma reachable_append (states : StateSet) (xs ys : List Nat) :
    reachable states (xs ++ ys) = reachable (reachable states xs) ys := by
  induction xs generalizing states with
  | nil => simp [reachable]
  | cons x xs ih =>
      simp only [List.cons_append, reachable]
      exact ih (states := stepSet x states)

def scanState (s : State) : Meldable.Decidable.State := (s.a.val, s.b.val)

def adjustPair : List Nat → List Bool → List Nat
  | x :: xs, takePair :: choices =>
      (x - pairTiles takePair) :: adjustPair xs choices
  | _, _ => []

def handOfList (xs : List Nat) (h : xs.length = 3 * n) : Hand n :=
  ⟨fun i => xs.get ⟨i.val, by omega⟩⟩

lemma adjustPair_length {xs : List Nat} {choices : List Bool}
    (h : choices.length = xs.length) : (adjustPair xs choices).length = xs.length := by
  induction xs generalizing choices with
  | nil => cases choices <;> simp [adjustPair] at h ⊢
  | cons x xs ih =>
      cases choices with
      | nil => simp at h
      | cons takePair choices => simp [adjustPair, ih (by simpa using h)]

lemma adjustPair_get {xs : List Nat} {choices : List Bool}
    (h : choices.length = xs.length) (i : Fin xs.length) :
    (adjustPair xs choices).get ⟨i.val, by simp [adjustPair_length h]⟩ =
      xs.get i - pairTiles (choices.get ⟨i.val, by omega⟩) := by
  induction xs generalizing choices with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      cases choices with
      | nil => simp at h
      | cons takePair choices =>
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [adjustPair]
          · simpa [adjustPair] using ih (by simpa using h) j

@[grind =]
lemma list_ofFn_handOfList (xs : List Nat) (h : xs.length = 3 * n) :
    List.ofFn (handOfList xs h) = xs := by
  apply List.ext_getElem
  · simp [handOfList, h]
  · intro i hi₁ hi₂
    simp [handOfList]

lemma replayChoices_all_false_of_true {s t : State} {xs : List Nat} {choices : List Bool}
    (hs : s.pairUsed = true) (h : replayChoices s xs choices = some t) :
    ∀ i : Fin choices.length, choices.get i = false := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil => intro i; exact Fin.elim0 i
      | cons takePair choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons takePair choices =>
          cases takePair with
          | true =>
              have hn : nextState s true x = none := by simp [nextState, hs]
              simp [replayChoices, hn] at h
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hn] using h
                  have hnext : next.pairUsed = true := by grind
                  intro i
                  refine Fin.cases ?_ (fun j => ?_) i
                  · rfl
                  · simpa using ih hnext hrest j

@[grind →]
lemma replayChoices_pair_witness {s t : State} {xs : List Nat} {choices : List Bool}
    (hlen : choices.length = xs.length)
    (h : replayChoices s xs choices = some t)
    (hs : s.pairUsed = false) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length, choices.get i = true ∧
      2 ≤ xs.get ⟨i.val, by simpa [hlen] using i.isLt⟩ ∧
      ∀ j, j ≠ i → choices.get j = false := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil =>
          cases h
          simp [hs] at ht
      | cons takePair choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp at hlen
      | cons takePair choices =>
          cases takePair with
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hn] using h
                  have hnext : next.pairUsed = false := by grind
                  obtain ⟨i, hi, hxi, huniq⟩ :=
                    ih (by simpa using hlen) hrest hnext
                  refine ⟨Fin.succ i, by simpa using hi, by simpa using hxi, ?_⟩
                  intro j
                  refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
                  apply huniq j
                  intro heq
                  exact hj (congrArg Fin.succ heq)
          | true =>
              cases hn : nextState s true x with
              | none => simp [replayChoices, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hn] using h
                  have hnext : next.pairUsed = true := by grind
                  have hfalse := replayChoices_all_false_of_true hnext hrest
                  refine ⟨0, rfl, by grind, ?_⟩
                  intro j
                  refine Fin.cases (fun hne => (hne rfl).elim) (fun j _ => ?_) j
                  simpa using hfalse j

lemma replayChoices_pair_index {s t : State} {xs : List Nat} {choices : List Bool}
    (hlen : choices.length = xs.length)
    (h : replayChoices s xs choices = some t)
    (hs : s.pairUsed = false) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length,
      choices.get i = true ∧ 2 ≤ xs.get ⟨i.val, by simpa [hlen] using i.isLt⟩ := by
  grind only [replayChoices_pair_witness]

lemma replayChoices_pair_unique {s t : State} {xs : List Nat} {choices : List Bool}
    (h : replayChoices s xs choices = some t)
    (hs : s.pairUsed = false) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length, choices.get i = true ∧
      ∀ j, j ≠ i → choices.get j = false := by
  have hlen := replayChoices_length h
  obtain ⟨i, hi, _, huniq⟩ := replayChoices_pair_witness hlen h hs ht
  exact ⟨i, hi, huniq⟩

lemma nextState_to_scanStep (s t : State) (takePair : Bool) (x : Nat)
    (h : nextState s takePair x = some t) :
    ∃ p : Meldable.Decidable.StepPlacement,
      Meldable.Decidable.step (scanState s) (x - pairTiles takePair) =
        some (p, scanState t) := by
  simp only [nextState] at h
  cases takePair with
  | false =>
      simp only [pairTiles, Bool.and_false, Bool.false_eq_true,
        Bool.or_false, ite_false, Nat.add_zero] at h
      have hneed : s.a.val + s.b.val ≤ x := by
        by_contra hnot
        simp only [if_neg hnot] at h
        cases h
      simp only [if_pos hneed] at h
      cases h
      let residual := x - (s.a.val + s.b.val)
      refine ⟨⟨residual / 3, ⟨residual % 3, Nat.mod_lt _ (by omega)⟩⟩, ?_⟩
      have hneed' : s.a.val + s.b.val ≤ x := by omega
      have hsub : x - pairTiles false - (s.a.val + s.b.val) = residual := by
        simp [pairTiles, residual]
      simp [Meldable.Decidable.step, scanState, pairTiles, hneed, residual]
  | true =>
      cases hp : s.pairUsed with
      | false =>
          simp only [pairTiles, hp, Bool.false_and, Bool.false_eq_true,
            Bool.or_true, ite_false, ite_true] at h
          have hneed : s.a.val + s.b.val + 2 ≤ x := by
            by_contra hnot
            simp only [if_neg hnot] at h
            cases h
          simp only [if_pos hneed] at h
          cases h
          let residual := x - (s.a.val + s.b.val + 2)
          refine ⟨⟨residual / 3, ⟨residual % 3, Nat.mod_lt _ (by omega)⟩⟩, ?_⟩
          have hneed' : s.a.val + s.b.val ≤ x - 2 := by omega
          have hsub : x - 2 - (s.a.val + s.b.val) = residual := by
            simp [residual]
            omega
          simp [Meldable.Decidable.step, scanState, pairTiles, hneed', hsub,
            residual]
      | true =>
          simp only [hp, Bool.true_and, ite_true] at h
          cases h

@[grind →]
lemma replayChoices_to_stepList {s t : State} {xs : List Nat} {choices : List Bool}
    (h : replayChoices s xs choices = some t) :
    ∃ ps, Meldable.Decidable.stepList (scanState s) (adjustPair xs choices) =
      some (ps, scanState t) := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil =>
          have hst : s = t := by simpa [replayChoices] using h
          subst t
          exact ⟨[], by simp [adjustPair, Meldable.Decidable.stepList]⟩
      | cons takePair choices => simp [replayChoices] at h
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons takePair choices =>
          cases hn : nextState s takePair x with
          | none => simp [replayChoices, hn] at h
          | some next =>
              have hrest : replayChoices next xs choices = some t := by
                simpa [replayChoices, hn] using h
              obtain ⟨p, hp⟩ := nextState_to_scanStep s next takePair x hn
              obtain ⟨ps, hps⟩ := ih hrest
              refine ⟨p :: ps, ?_⟩
              simp [adjustPair, Meldable.Decidable.stepList, hp, hps]

lemma scanStep_to_nextState (s t : State) (p : Meldable.Decidable.StepPlacement) (x : Nat)
    (h : Meldable.Decidable.step (scanState s) x = some (p, scanState t)) :
    nextState s false x = some {t with pairUsed := s.pairUsed} := by
  have hr := (Meldable.Decidable.step_eq_some_iff_replay (scanState s) x p
    (scanState t)).mp h
  simp only [Meldable.Decidable.replay, scanState, nextState, pairTiles] at hr ⊢
  grind

lemma scanStep_to_nextState_pair (s t : State) (p : Meldable.Decidable.StepPlacement)
    (x : Nat) (hs : s.pairUsed = false)
    (h : Meldable.Decidable.step (scanState s) x = some (p, scanState t)) :
    nextState s true (x + 2) = some {t with pairUsed := true} := by
  have hr := (Meldable.Decidable.step_eq_some_iff_replay (scanState s) x p
    (scanState t)).mp h
  simp only [Meldable.Decidable.replay, scanState, nextState, pairTiles, hs] at hr ⊢
  grind

def advance (s : State) (p : Meldable.Decidable.StepPlacement) : State :=
  ⟨p.seqNum, s.a, s.pairUsed⟩

def traceState : State → List Meldable.Decidable.StepPlacement → State
  | s, [] => s
  | s, p :: ps => traceState (advance s p) ps

def noPairChoices : List Meldable.Decidable.StepPlacement → List Bool
  | [] => []
  | _ :: ps => false :: noPairChoices ps

def pairChoicesAt : List Meldable.Decidable.StepPlacement → Nat → List Bool
  | [], _ => []
  | _ :: ps, 0 => true :: noPairChoices ps
  | _ :: ps, k + 1 => false :: pairChoicesAt ps k

def addPairAt : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, 0 => (x + 2) :: xs
  | x :: xs, k + 1 => x :: addPairAt xs k

@[simp, grind =]
lemma addPairAt_length (xs : List Nat) (k : Nat) : (addPairAt xs k).length = xs.length := by
  induction xs generalizing k with
  | nil => simp [addPairAt]
  | cons x xs ih => cases k <;> simp [addPairAt, ih]

lemma addPairAt_get (xs : List Nat) (k : Nat) (i : Fin xs.length) :
    (addPairAt xs k).get ⟨i.val, by simp⟩ =
      xs.get i + if i.val = k then 2 else 0 := by
  induction xs generalizing k with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · cases k <;> simp [addPairAt]
      · cases k with
        | zero => simp [addPairAt]
        | succ k => simpa [addPairAt] using ih k i

@[grind =]
lemma list_ofFn_add_pair (d : Hand n) (i : Fin (3 * n)) :
    List.ofFn (d + pair i) = addPairAt (List.ofFn d) i.val := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    let jf : Fin (List.ofFn d).length := ⟨j, by simpa using hj₁⟩
    have hget := addPairAt_get (List.ofFn d) i.val jf
    simpa [jf, add_apply, pair_apply] using hget.symm

@[simp, grind =]
lemma scanState_advance (s : State) (p : Meldable.Decidable.StepPlacement) :
    scanState (advance s p) = (Meldable.Decidable.replay (scanState s) p).2 := by
  simp [scanState, advance, Meldable.Decidable.replay]

@[simp, grind =]
lemma scanState_traceState (s : State) (ps : List Meldable.Decidable.StepPlacement) :
    scanState (traceState s ps) =
      (Meldable.Decidable.replayList (scanState s) ps).2 := by
  induction ps generalizing s with
  | nil => simp [traceState, Meldable.Decidable.replayList]
  | cons p ps ih => simp [traceState, Meldable.Decidable.replayList, ih]

@[simp, grind =]
lemma traceState_pairUsed (s : State) (ps : List Meldable.Decidable.StepPlacement) :
    (traceState s ps).pairUsed = s.pairUsed := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simpa [traceState, advance] using ih (advance s p)

@[simp]
lemma nextState_replay_false (s : State) (p : Meldable.Decidable.StepPlacement) :
    nextState s false (Meldable.Decidable.replay (scanState s) p).1 =
      some (advance s p) := by
  apply scanStep_to_nextState s (advance s p) p
  exact Meldable.Decidable.step_replay (scanState s) p

@[simp]
lemma nextState_replay_true (s : State) (p : Meldable.Decidable.StepPlacement)
    (hs : s.pairUsed = false) :
    nextState s true ((Meldable.Decidable.replay (scanState s) p).1 + 2) =
      some (advance {s with pairUsed := true} p) := by
  apply scanStep_to_nextState_pair s (advance s p) p _ hs
  exact Meldable.Decidable.step_replay (scanState s) p

lemma replayChoices_noPair_replayList
    (s : State) (ps : List Meldable.Decidable.StepPlacement) :
    replayChoices s (Meldable.Decidable.replayList (scanState s) ps).1
        (noPairChoices ps) = some (traceState s ps) := by
  induction ps generalizing s with
  | nil => simp [Meldable.Decidable.replayList, noPairChoices, traceState, replayChoices]
  | cons p ps ih =>
      have hn := nextState_replay_false s p
      simpa only [Meldable.Decidable.replayList, noPairChoices, traceState, replayChoices,
        hn, Option.bind_eq_bind, Option.bind_some, scanState_advance] using
        ih (advance s p)

lemma replayChoices_pair_replayList
    (s : State) (ps : List Meldable.Decidable.StepPlacement)
    (k : Nat) (hk : k < ps.length) (hs : s.pairUsed = false) :
    replayChoices s
        (addPairAt (Meldable.Decidable.replayList (scanState s) ps).1 k)
        (pairChoicesAt ps k) =
      some (traceState {s with pairUsed := true} ps) := by
  induction ps generalizing s k with
  | nil => simp at hk
  | cons p ps ih =>
      cases k with
      | zero =>
          have hn := nextState_replay_true s p hs
          simp only [Meldable.Decidable.replayList, addPairAt, pairChoicesAt, replayChoices]
          rw [hn]
          simp only [Option.bind_eq_bind, Option.bind_some]
          simpa [scanState, advance, traceState] using
            replayChoices_noPair_replayList (advance {s with pairUsed := true} p) ps
      | succ k =>
          have hk' : k < ps.length := by simpa using hk
          have hn := nextState_replay_false s p
          simp only [Meldable.Decidable.replayList, addPairAt, pairChoicesAt, replayChoices]
          rw [hn]
          simp only [Option.bind_eq_bind, Option.bind_some]
          simpa [scanState, advance, traceState] using ih (s := advance s p) k hk' hs

def DPWinning (c : Hand n) : Prop :=
  Hand.size c = 3 * n + 5 ∧
    ∃ choices,
      replayChoices State.init (List.ofFn c) choices = some State.final

lemma winning_to_dpWinning {c : Hand n} (h : Winning c) : DPWinning c := by
  rcases h with ⟨hcsize, d, i, hdmeld, hcd⟩
  refine ⟨hcsize, ?_⟩
  obtain ⟨p, hp, hcanonical⟩ := (Meldable.iff_exists_canonical_witness d).mp hdmeld
  let ps := Meldable.Decidable.disjoinCanonicalPlacement p hcanonical
  have hreplay := Meldable.Decidable.replayList_disjoinCanonicalPlacement p hcanonical
  have hvalues :
      (Meldable.Decidable.replayList (0, 0) ps).1 = List.ofFn d := by
    have hfst := congrArg Prod.fst hreplay
    change p.toHand = d at hp
    rw [hp] at hfst
    simpa [ps] using hfst
  have hfinal : (Meldable.Decidable.replayList (0, 0) ps).2 = (0, 0) := by
    have hsnd := congrArg Prod.snd hreplay
    simpa [ps] using hsnd
  have hk : i.val < ps.length := by
    simp [ps, Meldable.Decidable.disjoinCanonicalPlacement]
  let initial : State := State.init
  have hrun := replayChoices_pair_replayList initial ps i.val hk rfl
  have hinput :
      addPairAt (Meldable.Decidable.replayList (scanState initial) ps).1 i.val =
        List.ofFn c := by
    rw [show scanState initial = (0, 0) by rfl, hvalues]
    rw [← list_ofFn_add_pair d i, hcd]
  have hstate : traceState {initial with pairUsed := true} ps = State.final := by
    have hscan :
        scanState (traceState {initial with pairUsed := true} ps) = (0, 0) := by
      rw [scanState_traceState]
      simpa [initial, State.init, scanState] using hfinal
    have hpair := traceState_pairUsed {initial with pairUsed := true} ps
    generalize ht : traceState {initial with pairUsed := true} ps = t at hscan hpair ⊢
    cases t with
    | mk a b p =>
        have ha : a = (0 : Fin 3) := by
          apply Fin.ext
          simpa [scanState] using congrArg Prod.fst hscan
        have hb : b = (0 : Fin 3) := by
          apply Fin.ext
          simpa [scanState] using congrArg Prod.snd hscan
        cases ha
        cases hb
        cases hpair
        rfl
  refine ⟨pairChoicesAt ps i.val, ?_⟩
  rw [hinput, hstate] at hrun
  simpa [initial] using hrun

lemma decide_dp (c : Hand n) :
    Mahjong.Hand.Winning.decide c = true ↔ DPWinning c := by
  by_cases hs : Hand.size c = 3 * n + 5
  · simp only [decide, hs, bne_self_eq_false,
      List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, DPWinning,
      true_and]
    have hloop :
        List.foldl (fun s x => stepSet x s) ((∅ : StateSet).insert State.init)
            (List.ofFn c) = reachable ((∅ : StateSet).insert State.init) (List.ofFn c) := by
      simpa using loop_reachable (List.ofFn c)
    simp only [emptyStateSet, Std.ExtHashSet.emptyWithCapacity_eq]
    rw [hloop]
    simp [mem_reachable, State.init, State.final]
  · simp [Mahjong.Hand.Winning.decide, DPWinning, hs]

lemma dpWinning_to_winning {c : Hand n} (h : DPWinning c) : Winning c := by
  rcases h with ⟨hcsize, choices, hchoices⟩
  have hlen : choices.length = (List.ofFn c).length := by
    grind
  have hlen' : choices.length = 3 * n := by simpa using hlen
  obtain ⟨i, hi, hxi, huniq⟩ :=
    replayChoices_pair_witness hlen hchoices rfl rfl
  let adjusted := adjustPair (List.ofFn c) choices
  have hadjusted : adjusted.length = 3 * n := by
    simp [adjusted, adjustPair_length hlen]
  let d : Hand n := handOfList adjusted hadjusted
  have hdlist : List.ofFn d = adjusted := by
    grind only [list_ofFn_handOfList]
  obtain ⟨ps, hstep⟩ := replayChoices_to_stepList hchoices
  have hscan : Meldable.Decidable.scanList (List.ofFn d) = some ps := by
    rw [hdlist]
    exact (Meldable.Decidable.scanList_eq_some_iff_stepList _ _).mpr hstep
  have hdmeld : Meldable d := by
    rw [Meldable.Decidable.scanHand_iff_meldable]
    have hne : Meldable.Decidable.scanList (List.ofFn d) ≠ none := by
      intro hnone
      rw [hscan] at hnone
      simp at hnone
    simp only [Meldable.Decidable.scanHand]
    split
    · exact (hne ‹_›).elim
    · simp
  have hi_lt : i.val < 3 * n := by omega
  let idx : Fin (3 * n) := ⟨i.val, hi_lt⟩
  have hcd : c = d + pair idx := by
    ext j
    have hj : j.val < (List.ofFn c).length := by simp
    let ji : Fin choices.length := ⟨j.val, by simp [hlen]⟩
    let jx : Fin (List.ofFn c).length := ⟨j.val, hj⟩
    have hgetj : adjusted.get ⟨j.val, by simp [adjusted, adjustPair_length hlen]⟩ =
        (List.ofFn c).get jx - pairTiles (choices.get ji) := by
      simpa [adjusted, ji, jx] using adjustPair_get hlen jx
    have hchoice : choices.get ji = if j = idx then true else false := by
      by_cases hji : j = idx
      · subst j
        simpa [ji, idx] using hi
      · have hne : ji ≠ i := by
          intro heq
          apply hji
          apply Fin.ext
          simpa [idx] using congrArg Fin.val heq
        rw [if_neg hji]
        exact huniq ji hne
    have hbase : d j = (List.ofFn c).get jx - pairTiles (choices.get ji) := by
      simpa [d, handOfList, jx, ji] using hgetj
    have hcx : (List.ofFn c).get jx = c j := by simp [jx]
    simp only [add_apply, pair_apply]
    by_cases hji : j = idx
    · subst j
      have hji_i : ji = i := by
        apply Fin.ext
        simp [ji, idx]
      have hxi'' : 2 ≤ c idx := by simpa [idx] using hxi
      rw [hbase, hcx]
      rw [hji_i, hi]
      simp [pairTiles]
      omega
    · rw [hbase, hcx]
      rw [hchoice]
      have hval : j.val ≠ idx.val := by
        intro hval
        exact hji (Fin.ext hval)
      simp [pairTiles, hji, hval]
  exact ⟨hcsize, d, idx, hdmeld, hcd⟩

/--
Correctness specification of the executable winning-hand decision procedure.
-/
theorem decide_spec (c : Hand n) :
    Mahjong.Hand.Winning.decide c = true ↔ Winning c := by
  rw [decide_dp]
  exact ⟨dpWinning_to_winning, winning_to_dpWinning⟩

instance (c : Hand n) : Decidable (Winning c) :=
  decidable_of_iff (Mahjong.Hand.Winning.decide c = true) (decide_spec c)

end Mahjong.Hand.Winning.Decidable
