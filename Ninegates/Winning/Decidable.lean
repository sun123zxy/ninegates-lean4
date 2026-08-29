import Ninegates.Winning.Decide
import Ninegates.Bitset.Spec
import Ninegates.Meldable.Decidable

/-!
# Correctness of the winning-hand decision procedure

This file records the executable specification and its correctness proof.
-/

namespace Mahjong.Hand.Winning.Decidable

variable {n : ℕ}

instance lawfulStateEncoder : Bitset.LawfulEncoder State where
  encode_injective := by
    intro x y h
    rcases x with ⟨a, b, p⟩
    rcases y with ⟨a', b', p'⟩
    change State.encode ⟨a, b, p⟩ = State.encode ⟨a', b', p'⟩ at h
    simp [State.encode] at h
    cases p <;> cases p' <;> grind

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
  | none => Bitset.empty
  | some t => Bitset.singleton t

lemma enc_iff (x y : State) :
    Bitset.Encoder.encode x = Bitset.Encoder.encode y ↔ x = y := by
  constructor
  · intro h
    exact Bitset.LawfulEncoder.encode_injective (α := State) h
  · exact congrArg Bitset.Encoder.encode

lemma step_eq_union (x : Nat) (s : State) :
    step x s = Bitset.union (choice x s false) (choice x s true) := by
  unfold step
  simp only [List.forIn_cons, Id.run_bind]
  by_cases h0 : s.a.val + s.b.val ≤ x
  · by_cases h1 : s.pairUsed = true
    · by_cases h2 : s.a.val + s.b.val + 2 ≤ x <;>
        simp [choice, nextState, pairTiles, h0, h1, Bitset.insert,
          Bitset.singleton, Bitset.union, Bitset.empty]
    · by_cases h2 : s.a.val + s.b.val + 2 ≤ x <;>
        simp [choice, nextState, pairTiles, h0, h1, h2, Bitset.singleton,
          Bitset.insert, Bitset.union, Bitset.empty]
  · by_cases h1 : s.pairUsed = true
    · by_cases h2 : s.a.val + s.b.val + 2 ≤ x <;>
        simp [choice, nextState, pairTiles, h0, h1, Bitset.insert,
          Bitset.singleton, Bitset.union, Bitset.empty]
    · by_cases h2 : s.a.val + s.b.val + 2 ≤ x <;>
        simp [choice, nextState, pairTiles, h0, h1, h2, Bitset.insert,
          Bitset.singleton, Bitset.union, Bitset.empty]

lemma mem_choice (x : Nat) (s t : State) (takePair : Bool) :
    Bitset.mem (choice x s takePair) t = true ↔
      nextState s takePair x = some t := by
  cases h : nextState s takePair x with
  | none => simp [choice, h]
  | some u => simp [choice, h, enc_iff]

lemma mem_step (x : Nat) (s t : State) :
    Bitset.mem (step x s) t = true ↔
      nextState s false x = some t ∨ nextState s true x = some t := by
  rw [step_eq_union]
  simp only [Bitset.mem_union_iff, mem_choice]

lemma state_all (s : State) : s ∈ State.all := by
  rcases s with ⟨a, b, p⟩
  cases p <;> simp [State.all]

lemma mem_fold_union (xs : List State) (f : State → StateSet) (acc : StateSet) (t : State) :
    Bitset.mem (xs.foldl (fun r q ↦ Bitset.union r (f q)) acc) t = true ↔
      Bitset.mem acc t = true ∨ ∃ q ∈ xs, Bitset.mem (f q) t = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons q qs ih =>
      simp only [List.foldl]
      rw [ih]
      simp only [Bitset.mem_union_iff, List.mem_cons]
      grind

lemma mem_fold_step (xs : List State) (x : Nat) (states : StateSet)
    (acc : StateSet) (t : State) :
    Bitset.mem
        (xs.foldl
          (fun result q =>
            if Bitset.mem states q = true then Bitset.union result (step x q) else result)
          acc)
        t = true ↔
      Bitset.mem acc t = true ∨
        ∃ q ∈ xs, Bitset.mem states q = true ∧ Bitset.mem (step x q) t = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons q qs ih =>
      simp only [List.foldl]
      rw [ih]
      by_cases hs : Bitset.mem states q = true
      · simp [hs]
        grind
      · simp [hs]

lemma mem_stepSet (x : Nat) (states : StateSet) (t : State) :
    Bitset.mem (stepSet x states) t = true ↔
      ∃ q : State, Bitset.mem states q = true ∧ Bitset.mem (step x q) t = true := by
  unfold stepSet
  rw [mem_fold_step]
  constructor
  · rintro (hacc | ⟨q, hqall, hq, hstep⟩)
    · simp at hacc
    · exact ⟨q, hq, hstep⟩
  · rintro ⟨q, hq, hstep⟩
    exact Or.inr ⟨q, state_all q, hq, hstep⟩

def replayChoices : State → List Nat → List Bool → Option State
  | s, [], [] => some s
  | s, x :: xs, takePair :: choices => do
      let t ← nextState s takePair x
      replayChoices t xs choices
  | _, _, _ => none

lemma replayChoices_length {s t : State} {xs : List Nat} {choices : List Bool}
    (h : replayChoices s xs choices = some t) : choices.length = xs.length := by
  induction xs generalizing s choices with
  | nil => cases choices <;> simp [replayChoices] at h ⊢
  | cons x xs ih =>
      cases choices with
      | nil => simp [replayChoices] at h
      | cons takePair choices =>
          cases hn : nextState s takePair x with
          | none => simp [replayChoices, hn] at h
          | some next =>
              have hr : replayChoices next xs choices = some t := by
                simpa [replayChoices, hn] using h
              simp [ih hr]

def reachable : StateSet → List Nat → StateSet
  | states, [] => states
  | states, x :: xs => reachable (stepSet x states) xs

lemma mem_reachable (states : StateSet) (xs : List Nat) (t : State) :
    Bitset.mem (reachable states xs) t = true ↔
      ∃ s, Bitset.mem states s = true ∧
        ∃ choices, replayChoices s xs choices = some t := by
  induction xs generalizing states with
  | nil =>
      change Bitset.mem states t = true ↔ _
      constructor
      · intro h
        exact ⟨t, h, [], rfl⟩
      · rintro ⟨s, hs, choices, hchoices⟩
        cases choices with
        | nil =>
            have hst : s = t := by simpa [replayChoices] using hchoices
            simpa [hst] using hs
        | cons takePair choices => simp [replayChoices] at hchoices
  | cons x xs ih =>
      rw [reachable, ih]
      constructor
      · rintro ⟨u, hu, choices, hrest⟩
        obtain ⟨s, hs, hstep⟩ := (mem_stepSet x states u).mp hu
        rcases (mem_step x s u).mp hstep with hfalse | htrue
        · exact ⟨s, hs, false :: choices, by simp [replayChoices, hfalse, hrest]⟩
        · exact ⟨s, hs, true :: choices, by simp [replayChoices, htrue, hrest]⟩
      · rintro ⟨s, hs, choices, hchoices⟩
        cases choices with
        | nil => simp [replayChoices] at hchoices
        | cons takePair choices =>
            cases hn : nextState s takePair x with
            | none => simp [replayChoices, hn] at hchoices
            | some u =>
                have hrest : replayChoices u xs choices = some t := by
                  simpa [replayChoices, hn] using hchoices
                have hmem : Bitset.mem (step x s) u = true := by
                  apply (mem_step x s u).mpr
                  cases takePair
                  · exact Or.inl hn
                  · exact Or.inr hn
                exact ⟨u, (mem_stepSet x states u).mpr ⟨s, hs, hmem⟩,
                  choices, hrest⟩

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
      let mut states : StateSet := Bitset.singleton State.init
      for x in xs do
        states := stepSet x states
      return states) = reachable (Bitset.singleton State.init) xs := by
  simpa using loop_reachable_from (Bitset.singleton State.init) xs

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

lemma list_ofFn_handOfList (xs : List Nat) (h : xs.length = 3 * n) :
    List.ofFn (handOfList xs h) = xs := by
  apply List.ext_getElem
  · simp [handOfList, h]
  · intro i hi₁ hi₂
    simp [handOfList]

lemma replayChoices_pair_index {s t : State} {xs : List Nat} {choices : List Bool}
    (hlen : choices.length = xs.length)
    (h : replayChoices s xs choices = some t)
    (hs : s.pairUsed = false) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length,
      choices.get i = true ∧ 2 ≤ xs.get ⟨i.val, by simpa [hlen] using i.isLt⟩ := by
  induction xs generalizing s choices with
  | nil =>
      cases choices with
      | nil =>
          have hst : s = t := by
            simpa [replayChoices] using h
          subst t
          simp [hs] at ht
      | cons takePair choices =>
          simp [replayChoices] at h
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
                  have hnext : next.pairUsed = false := by
                    simp [nextState, hs] at hn
                    grind
                  obtain ⟨i, hi, hxi⟩ := ih (by simpa using hlen) hrest hnext
                  refine ⟨Fin.succ i, ?_, ?_⟩
                  · simpa using hi
                  · simpa using hxi
          | true =>
              cases hn : nextState s true x with
              | none => simp [replayChoices, hn] at h
              | some next =>
                  refine ⟨0, rfl, ?_⟩
                  have hneed : s.a.val + s.b.val + 2 ≤ x := by
                    simp [nextState, hs, pairTiles] at hn
                    omega
                  have hx : 2 ≤ x := by omega
                  simpa using hx

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
                  have hnext : next.pairUsed = true := by
                    simp [nextState, hs] at hn
                    grind
                  intro i
                  refine Fin.cases ?_ (fun j => ?_) i
                  · rfl
                  · simpa using ih hnext hrest j

lemma replayChoices_pair_unique {s t : State} {xs : List Nat} {choices : List Bool}
    (h : replayChoices s xs choices = some t)
    (hs : s.pairUsed = false) (ht : t.pairUsed = true) :
    ∃ i : Fin choices.length, choices.get i = true ∧
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
      | nil => simp [replayChoices] at h
      | cons takePair choices =>
          cases takePair with
          | false =>
              cases hn : nextState s false x with
              | none => simp [replayChoices, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hn] using h
                  have hnext : next.pairUsed = false := by
                    simp [nextState, hs] at hn
                    grind
                  obtain ⟨i, hi, huniq⟩ := ih hrest hnext
                  refine ⟨Fin.succ i, by simpa using hi, ?_⟩
                  intro j
                  refine Fin.cases ?_ (fun j => ?_) j
                  · intro _
                    rfl
                  · intro hj
                    apply huniq
                    intro heq
                    apply hj
                    exact congrArg Fin.succ heq
          | true =>
              cases hn : nextState s true x with
              | none => simp [replayChoices, hn] at h
              | some next =>
                  have hrest : replayChoices next xs choices = some t := by
                    simpa [replayChoices, hn] using h
                  have hnext : next.pairUsed = true := by
                    simp [nextState, hs] at hn
                    grind
                  have hfalse := replayChoices_all_false_of_true hnext hrest
                  refine ⟨0, rfl, ?_⟩
                  intro j
                  refine Fin.cases ?_ (fun j => ?_) j
                  · intro hne
                    exact False.elim (hne rfl)
                  · intro _
                    simpa using hfalse j

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

@[simp]
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

lemma list_ofFn_add_pair (d : Hand n) (i : Fin (3 * n)) :
    List.ofFn (d + pair i) = addPairAt (List.ofFn d) i.val := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    let jf : Fin (List.ofFn d).length := ⟨j, by simpa using hj₁⟩
    have hget := addPairAt_get (List.ofFn d) i.val jf
    simpa [jf, add_apply, pair_apply] using hget.symm

@[simp]
lemma scanState_advance (s : State) (p : Meldable.Decidable.StepPlacement) :
    scanState (advance s p) = (Meldable.Decidable.replay (scanState s) p).2 := by
  simp [scanState, advance, Meldable.Decidable.replay]

@[simp]
lemma scanState_traceState (s : State) (ps : List Meldable.Decidable.StepPlacement) :
    scanState (traceState s ps) =
      (Meldable.Decidable.replayList (scanState s) ps).2 := by
  induction ps generalizing s with
  | nil => simp [traceState, Meldable.Decidable.replayList]
  | cons p ps ih => simp [traceState, Meldable.Decidable.replayList, ih]

@[simp]
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
  Valid c ∧ Hand.size c = 3 * n + 5 ∧
    ∃ choices,
      replayChoices State.init (List.ofFn c) choices = some State.final

lemma winning_to_dpWinning {c : Hand n} (h : Winning c) : DPWinning c := by
  rcases h with ⟨hcvalid, hcsize, d, i, hdmeld, hcd⟩
  refine ⟨hcvalid, hcsize, ?_⟩
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
  by_cases hv : Valid c
  · by_cases hs : Hand.size c = 3 * n + 5
    · simp only [decide, hv, decide_true, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, hs, bne_self_eq_false, List.forIn_pure_yield_eq_foldl,
        bind_pure_comp, map_pure, Id.run_pure, DPWinning, true_and]
      have hloop :
          List.foldl (fun s x => stepSet x s) (Bitset.singleton State.init)
              (List.ofFn c) = reachable (Bitset.singleton State.init) (List.ofFn c) := by
        simpa using loop_reachable (List.ofFn c)
      rw [hloop]
      rw [mem_reachable]
      simp [State.init, State.final, enc_iff]
    · simp [Mahjong.Hand.Winning.decide, DPWinning, hv, hs]
  · simp [Mahjong.Hand.Winning.decide, DPWinning, hv]

lemma dpWinning_to_winning {c : Hand n} (h : DPWinning c) : Winning c := by
  rcases h with ⟨hcvalid, hcsize, choices, hchoices⟩
  have hlen : choices.length = (List.ofFn c).length := replayChoices_length hchoices
  have hlen' : choices.length = 3 * n := by simpa using hlen
  obtain ⟨i, hi, huniq⟩ := replayChoices_pair_unique hchoices rfl rfl
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
    simp [adjusted, adjustPair_length hlen]
  let d : Hand n := handOfList adjusted hadjusted
  have hdlist : List.ofFn d = adjusted := list_ofFn_handOfList adjusted hadjusted
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
  exact ⟨hcvalid, hcsize, d, idx, hdmeld, hcd⟩

/-- Correctness specification of the executable winning-hand decision procedure.

This is the sole algorithm-specific obligation needed by the `Decidable` bridge;
the proof is intentionally deferred while the executable structure is stabilized.
-/
theorem decide_spec (c : Hand n) :
    Mahjong.Hand.Winning.decide c = true ↔ Winning c := by
  rw [decide_dp]
  exact ⟨dpWinning_to_winning, winning_to_dpWinning⟩

instance (c : Hand n) : Decidable (Winning c) :=
  decidable_of_iff (Mahjong.Hand.Winning.decide c = true) (decide_spec c)

end Mahjong.Hand.Winning.Decidable
