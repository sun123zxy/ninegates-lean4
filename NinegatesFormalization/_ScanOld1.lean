import NinegatesFormalization.Basic
import Std.Tactic.Do

namespace Mahjong.Hand.Meldable.ScanNew

open Std.Do

@[ext]
structure StepPlacement where
  tripNum : ℕ
  seqNum : ℕ
deriving DecidableEq, Repr

abbrev ScanState := ℕ × ℕ

structure ScanStore where
  state : ScanState
  steps : List StepPlacement
deriving DecidableEq, Repr

inductive Failure where
  | failEarly
  | failFinally
deriving DecidableEq, Repr

abbrev ScanM := EStateM Failure ScanStore

def scanStep (x : ℕ) : ScanM Unit := do
  let store ← get
  let s := store.state
  unless s.1 + s.2 ≤ x do
    throw .failEarly
  let rem := x - (s.1 + s.2)
  let p : StepPlacement := ⟨rem / 3, rem % 3⟩
  let next : ScanStore :=
    { state := (p.seqNum, s.1), steps := store.steps ++ [p] }
  set next

private def finish : ScanM Unit := do
  unless (← get).state = (0, 0) do
    throw .failFinally

def scan : List ℕ → ScanM Unit
  | [] => finish
  | x :: xs => do
      scanStep x
      scan xs

abbrev ScanResult := EStateM.Result Failure ScanStore Unit

namespace ScanResult

def isOk : ScanResult → Bool
  | .ok _ _ => true
  | .error _ _ => false

end ScanResult

def scanList (xs : List ℕ) : ScanResult :=
  (scan xs).run ⟨(0, 0), []⟩

def scanHand (c : Hand n) : ScanResult :=
  scanList (List.ofFn fun i ↦ c i)

def realizeFrom : ScanState → List StepPlacement → List ℕ × ScanState
  | s, [] => ([], s)
  | s, p :: ps =>
      let out := realizeFrom (p.seqNum, s.1) ps
      ((s.1 + s.2 + 3 * p.tripNum + p.seqNum) :: out.1, out.2)

private theorem length_realizeFrom (s : ScanState)
    (steps : List StepPlacement) :
    (realizeFrom s steps).1.length = steps.length := by
  induction steps generalizing s with
  | nil => simp [realizeFrom]
  | cons p ps ih => simp [realizeFrom, ih]

def IsListWitness (steps : List StepPlacement) (xs : List ℕ) : Prop :=
  realizeFrom (0, 0) steps = (xs, (0, 0))

def ListMeldable (xs : List ℕ) : Prop :=
  ∃ steps, IsListWitness steps xs

private def compensate (q : ℕ) : List StepPlacement → List StepPlacement
  | p₁ :: p₂ :: ps =>
      { p₁ with tripNum := p₁.tripNum + q } ::
        { p₂ with tripNum := p₂.tripNum + q } :: ps
  | ps => ps

set_option linter.flexible false in
private theorem realizeFrom_mod (z a : ℕ) (steps : List StepPlacement) (xs : List ℕ)
    (h : realizeFrom (z, a) steps = (xs, (0, 0))) :
    realizeFrom (z % 3, a) (compensate (z / 3) steps) = (xs, (0, 0)) := by
  have hz := Nat.mod_add_div z 3
  cases steps with
  | nil =>
      simp [realizeFrom, compensate] at h ⊢
      rcases h with ⟨rfl, rfl, rfl⟩
      simp
  | cons p steps =>
      cases steps with
      | nil =>
          simp [realizeFrom, compensate] at h ⊢
          rcases h with ⟨rfl, hp, rfl⟩
          simp [hp]
      | cons p' steps =>
          simp [realizeFrom, compensate] at h ⊢
          rcases h with ⟨rfl, hend⟩
          refine ⟨?_, hend⟩
          congr 2 <;> simp [Nat.mul_add] <;> omega

@[spec]
theorem scanStep_spec (x : ℕ) (initial : ScanStore) :
    ⦃fun store => ⌜store = initial⌝⦄
      scanStep x
    ⦃post⟨
      (fun _ store => ⌜initial.state.1 + initial.state.2 ≤ x ∧
        store =
          let rem := x - (initial.state.1 + initial.state.2)
          let p : StepPlacement := ⟨rem / 3, rem % 3⟩
          { state := (p.seqNum, initial.state.1),
            steps := initial.steps ++ [p] }⌝),
      (fun e store => ⌜e = .failEarly ∧
        ¬initial.state.1 + initial.state.2 ≤ x ∧ store = initial⌝)⟩⦄ := by
  mvcgen [scanStep] with grind

@[spec]
private theorem finish_spec (initial : ScanStore) :
    ⦃fun store => ⌜store = initial⌝⦄
      finish
    ⦃post⟨
      (fun _ store => ⌜initial.state = (0, 0) ∧ store = initial⌝),
      (fun e store => ⌜e = .failFinally ∧ initial.state ≠ (0, 0) ∧
        store = initial⌝)⟩⦄ := by
  mvcgen [finish] with grind

private def Realizable (s : ScanState) (xs : List ℕ) : Prop :=
  ∃ steps, realizeFrom s steps = (xs, (0, 0))

@[local grind =]
private theorem listMeldable_eq_realizable (xs : List ℕ) :
    ListMeldable xs = Realizable (0, 0) xs := by
  rfl

private theorem realizeFrom_scanStep (s : ScanState) (steps : List StepPlacement)
    (x : ℕ) (xs : List ℕ) (hle : s.1 + s.2 ≤ x)
    (h : realizeFrom ((x - (s.1 + s.2)) % 3, s.1) steps =
      (xs, (0, 0))) :
    realizeFrom s
      (⟨(x - (s.1 + s.2)) / 3, (x - (s.1 + s.2)) % 3⟩ :: steps) =
      (x :: xs, (0, 0)) := by
  have hdiv := Nat.mod_add_div (x - (s.1 + s.2)) 3
  simp [realizeFrom, h]
  omega

@[local grind =]
private theorem realizable_nil (s : ScanState) :
    Realizable s [] = (s = (0, 0)) := by
  apply propext
  constructor
  · rintro ⟨steps, hsteps⟩
    cases steps <;> grind [realizeFrom]
  · intro h
    exact ⟨[], by simp [realizeFrom, h]⟩

@[local grind =]
private theorem realizable_cons (s : ScanState) (x : ℕ) (xs : List ℕ) :
    Realizable s (x :: xs) =
      (s.1 + s.2 ≤ x ∧
        Realizable ((x - (s.1 + s.2)) % 3, s.1) xs) := by
  apply propext
  constructor
  · rintro ⟨steps, hsteps⟩
    cases steps with
    | nil => grind [realizeFrom]
    | cons p ps =>
        have hxs := congrArg Prod.fst hsteps
        have hend := congrArg Prod.snd hsteps
        simp only [realizeFrom] at hxs hend
        have hx := List.cons.inj hxs |>.1
        have htailList := List.cons.inj hxs |>.2
        have htail : realizeFrom (p.seqNum, s.1) ps = (xs, (0, 0)) :=
          Prod.ext htailList hend
        have hle : s.1 + s.2 ≤ x := by omega
        refine ⟨hle, compensate (p.seqNum / 3) ps, ?_⟩
        have hrem : x - (s.1 + s.2) = 3 * p.tripNum + p.seqNum := by omega
        rw [hrem]
        simpa [Nat.add_mod] using realizeFrom_mod p.seqNum s.1 ps xs htail
  · rintro ⟨hle, steps, hsteps⟩
    exact ⟨_, realizeFrom_scanStep s steps x xs hle hsteps⟩

private def ScanSuccess (initial final : ScanStore) (xs : List ℕ) : Prop :=
  ∃ suffix,
    final =
      { state := (0, 0),
        steps := initial.steps ++ suffix } ∧
    realizeFrom initial.state suffix = (xs, (0, 0))

@[local grind ←]
private theorem scanSuccess_nil (initial : ScanStore)
    (h : initial.state = (0, 0)) : ScanSuccess initial initial [] := by
  rcases initial with ⟨state, steps⟩
  have hstate : state = (0, 0) := h
  subst state
  exact ⟨[], by simp, by simp [realizeFrom]⟩

@[local grind ←]
private theorem scanSuccess_cons (initial final : ScanStore) (x : ℕ)
    (xs : List ℕ) (hle : initial.state.1 + initial.state.2 ≤ x)
    (h : ScanSuccess
      { state := ((x - (initial.state.1 + initial.state.2)) % 3, initial.state.1),
        steps := initial.steps ++
          [⟨(x - (initial.state.1 + initial.state.2)) / 3,
            (x - (initial.state.1 + initial.state.2)) % 3⟩] }
      final xs) : ScanSuccess initial final (x :: xs) := by
  rcases h with ⟨suffix, hfinal, htail⟩
  let rem := x - (initial.state.1 + initial.state.2)
  let p : StepPlacement := ⟨rem / 3, rem % 3⟩
  refine ⟨p :: suffix, ?_, ?_⟩
  · simpa [p, rem, List.append_assoc] using hfinal
  · exact realizeFrom_scanStep initial.state suffix x xs hle (by
      simpa [p, rem] using htail)

private theorem scan_spec_aux (xs : List ℕ) (initial : ScanStore) :
    ⦃fun store => ⌜store = initial⌝⦄
      scan xs
    ⦃post⟨
      (fun _ final => ⌜ScanSuccess initial final xs⌝),
      (fun _ _ => ⌜¬Realizable initial.state xs⌝)⟩⦄ := by
  induction xs generalizing initial <;>
    mvcgen [scan, *] with grind [realizeFrom, List.append_assoc]

@[spec]
theorem scan_spec (xs : List ℕ) (initial : ScanStore) :
    ⦃fun store => ⌜store = initial⌝⦄
      scan xs
    ⦃post⟨
      (fun _ final => ⌜∃ suffix,
        final =
          { state := (0, 0),
            steps := initial.steps ++ suffix } ∧
        realizeFrom initial.state suffix = (xs, (0, 0))⌝),
      (fun _ _ => ⌜¬∃ steps,
        realizeFrom initial.state steps = (xs, (0, 0))⌝)⟩⦄ := by
  simpa [ScanSuccess, Realizable] using scan_spec_aux xs initial

theorem iff_scanList (xs : List ℕ) :
    ListMeldable xs ↔ (scanList xs).isOk := by
  refine EStateM.of_wp_run_eq (x := scanList xs) (prog := scan xs)
    (s := ⟨(0, 0), []⟩) rfl
    (fun r => ListMeldable xs ↔ ScanResult.isOk r = true) ?_
  mvcgen [scan_spec_aux] with grind [ScanResult.isOk, Realizable]

namespace Placement

private def seqAt (p : Placement n) (i : ℕ) : ℕ :=
  if h : i < 3 * n - 2 then p.seqNum ⟨i, h⟩ else 0

private def pending (p : Placement n) (i : ℕ) : ScanState :=
  (if 0 < i then seqAt p (i - 1) else 0,
    if 1 < i then seqAt p (i - 2) else 0)

private lemma sum_seq_offset (p : Placement n) (k : Fin (3 * n))
    (d : ℕ) (hd : d ≤ 2) :
    (∑ j, p.seqNum j *
      (if k = (⟨j.val + d, by omega⟩ : Fin (3 * n)) then 1 else 0)) =
      if d ≤ k.val then seqAt p (k.val - d) else 0 := by
  by_cases hdk : d ≤ k.val
  · rw [if_pos hdk]
    unfold seqAt
    split
    next hbound =>
      rw [Finset.sum_eq_single ⟨k.val - d, hbound⟩]
      · have heq :
            k = (⟨(k.val - d) + d, by omega⟩ : Fin (3 * n)) := by
          apply Fin.ext
          change k.val = (k.val - d) + d
          omega
        rw [if_pos heq, mul_one]
      · intro j _ hj
        have hne : k ≠ (⟨j.val + d, by omega⟩ : Fin (3 * n)) := by
          intro heq
          apply hj
          apply Fin.ext
          have hv := congrArg Fin.val heq
          change k.val = j.val + d at hv
          change j.val = k.val - d
          omega
        simp [hne]
      · simp
    next hbound =>
      apply Finset.sum_eq_zero
      intro j _
      have hne : k ≠ (⟨j.val + d, by omega⟩ : Fin (3 * n)) := by
        intro heq
        apply hbound
        have hv := congrArg Fin.val heq
        change k.val = j.val + d at hv
        have hidx : k.val - d = j.val := by omega
        rw [hidx]
        exact j.isLt
      simp [hne]
  · rw [if_neg hdk]
    apply Finset.sum_eq_zero
    intro j _
    have hne : k ≠ (⟨j.val + d, by omega⟩ : Fin (3 * n)) := by
      intro heq
      apply hdk
      have hv := congrArg Fin.val heq
      change k.val = j.val + d at hv
      omega
    simp [hne]

private lemma toHand_apply_local (p : Placement n) (k : Fin (3 * n)) :
    p.toHand k =
      (pending p k.val).1 + (pending p k.val).2 +
        3 * p.tripNum k + seqAt p k.val := by
  have htrip :
      (∑ i, (p.tripNum i • Hand.triplet i) k) = 3 * p.tripNum k := by
    simp [Hand.triplet, Hand.single, mul_comm]
  have h0 :
      (∑ j, if k = (⟨j.val, by omega⟩ : Fin (3 * n)) then p.seqNum j else 0) =
        seqAt p k.val := by
    simpa using sum_seq_offset p k 0 (by omega)
  have h1 :
      (∑ j, if k = (⟨j.val + 1, by omega⟩ : Fin (3 * n)) then p.seqNum j else 0) =
        if 0 < k.val then seqAt p (k.val - 1) else 0 := by
    have h := sum_seq_offset p k 1 (by omega)
    by_cases hk : 1 ≤ k.val
    · have hk' : 0 < k.val := by omega
      simpa [hk, hk'] using h
    · have hk' : ¬0 < k.val := by omega
      simpa [hk, hk'] using h
  have h2 :
      (∑ j, if k = (⟨j.val + 2, by omega⟩ : Fin (3 * n)) then p.seqNum j else 0) =
        if 1 < k.val then seqAt p (k.val - 2) else 0 := by
    have h := sum_seq_offset p k 2 (by omega)
    by_cases hk : 2 ≤ k.val
    · have hk' : 1 < k.val := by omega
      simpa [hk, hk'] using h
    · have hk' : ¬1 < k.val := by omega
      simpa [hk, hk'] using h
  rw [Placement.toHand_apply, htrip]
  simp only [Hand.sequence, Hand.single, Hand.mk_apply, smul_apply, add_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [h0, h1, h2]
  simp only [pending]
  omega

private lemma pending_zero (p : Placement n) : pending p 0 = (0, 0) := by
  simp [pending]

private lemma pending_succ (p : Placement n) (i : ℕ) :
    pending p (i + 1) = (seqAt p i, (pending p i).1) := by
  cases i <;> simp [pending]

private lemma pending_end (p : Placement n) : pending p (3 * n) = (0, 0) := by
  by_cases hn : n = 0
  · subst n
    simp [pending]
  · have hnpos : 0 < n := by omega
    have hlast : ¬3 * n - 1 < 3 * n - 2 := by omega
    simp [pending, seqAt, hnpos, hlast]

private def steps (p : Placement n) : List StepPlacement :=
  List.ofFn fun i : Fin (3 * n) => ⟨p.tripNum i, seqAt p i.val⟩

private lemma getElem_steps (p : Placement n) (i : ℕ)
    (hi : i < (steps p).length) :
    (steps p)[i] =
      ⟨p.tripNum ⟨i, by simpa [steps] using hi⟩, seqAt p i⟩ := by
  simp [steps]

private theorem realizeFrom_steps_drop (p : Placement n) (i : ℕ)
    (hi : i ≤ 3 * n) :
    realizeFrom (pending p i) ((steps p).drop i) =
      ((List.ofFn fun k => p.toHand k).drop i, (0, 0)) := by
  induction hi using Nat.decreasingInduction with
  | self =>
      rw [List.drop_of_length_le (by simp [steps]),
        List.drop_of_length_le (by simp)]
      simp [realizeFrom, pending_end]
  | of_succ i hi ih =>
      have histeps : i < (steps p).length := by simp [steps]; omega
      have hicounts : i < (List.ofFn fun k => p.toHand k).length := by
        simp
        omega
      rw [List.drop_eq_getElem_cons histeps,
        List.drop_eq_getElem_cons hicounts]
      rw [getElem_steps, List.getElem_ofFn]
      simp only [realizeFrom]
      rw [← pending_succ, ih, toHand_apply_local]

private theorem toListWitness (p : Placement n) :
    IsListWitness (steps p) (List.ofFn fun k => p.toHand k) := by
  unfold IsListWitness
  simpa [pending_zero] using realizeFrom_steps_drop p 0 (by omega)

private def ofSteps (ss : List StepPlacement) (hlen : ss.length = 3 * n) :
    Placement n where
  tripNum i := (ss[i.val]'(by omega)).tripNum
  seqNum i := (ss[i.val]'(by omega)).seqNum

private lemma realizeFrom_append_two (s : ScanState)
    (pref : List StepPlacement) (p q : StepPlacement) :
    (realizeFrom s (pref ++ [p, q])).2 = (q.seqNum, p.seqNum) := by
  induction pref generalizing s with
  | nil => simp [realizeFrom]
  | cons r rs ih => simpa [realizeFrom] using ih (r.seqNum, s.1)

private theorem steps_ofSteps_eq (ss : List StepPlacement)
    (hlen : ss.length = 3 * n)
    (hend : (realizeFrom (0, 0) ss).2 = (0, 0)) :
    steps (ofSteps ss hlen : Placement n) = ss := by
  by_cases hn : n = 0
  · subst n
    have : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst ss
    simp [steps]
  · have hnpos : 0 < n := by omega
    let pref := ss.take (3 * n - 2)
    have hsuffixLen : (ss.drop (3 * n - 2)).length = 2 := by
      simp [hlen]
      omega
    rcases List.length_eq_two.mp hsuffixLen with ⟨p, q, hsuffix⟩
    have hsplit : ss = pref ++ [p, q] := by
      dsimp [pref]
      rw [← hsuffix, List.take_append_drop]
    have hpq : (q.seqNum, p.seqNum) = (0, 0) := by
      rw [hsplit, realizeFrom_append_two] at hend
      exact hend
    have hpzero : p.seqNum = 0 := congrArg Prod.snd hpq
    have hqzero : q.seqNum = 0 := congrArg Prod.fst hpq
    have hprefLen : pref.length = 3 * n - 2 := by
      simp [pref, hlen]
    apply List.ext_getElem
    · simp [steps, hlen]
    · intro i hi₁ hi₂
      simp only [steps, List.getElem_ofFn]
      apply StepPlacement.ext
      · rfl
      · unfold seqAt
        split
        next hibound => rfl
        next hibound =>
          have hi : i = 3 * n - 2 ∨ i = 3 * n - 1 := by omega
          rcases hi with hi | hi
          · subst i
            have hget : ss[3 * n - 2] = p := by
              exact List.getElem_of_append hsplit hprefLen
            rw [hget, hpzero]
          · subst i
            have hget : ss[3 * n - 1] = q := by
              apply List.getElem_of_append (l₁ := pref ++ [p]) (l₂ := [])
              · simpa [List.append_assoc] using hsplit
              · simp [hprefLen]
                omega
            rw [hget, hqzero]

end Placement

private theorem meldable_iff_listMeldable (c : Hand n) :
    Meldable c ↔ ListMeldable (List.ofFn fun i => c i) := by
  constructor
  · rintro ⟨p, hp⟩
    unfold IsWitness at hp
    subst c
    exact ⟨Placement.steps p, Placement.toListWitness p⟩
  · rintro ⟨ss, hss⟩
    have hlen : ss.length = 3 * n := by
      have hlenRealize := length_realizeFrom (0, 0) ss
      rw [hss] at hlenRealize
      simpa using hlenRealize.symm
    have hend : (realizeFrom (0, 0) ss).2 = (0, 0) := by
      rw [hss]
    let p : Placement n := Placement.ofSteps ss hlen
    have hround : Placement.steps p = ss :=
      Placement.steps_ofSteps_eq ss hlen hend
    have hp := Placement.toListWitness p
    unfold IsListWitness at hp hss
    rw [hround] at hp
    have hlists : List.ofFn (fun i => p.toHand i) =
        List.ofFn (fun i => c i) := congrArg Prod.fst (hp.symm.trans hss)
    refine ⟨p, ?_⟩
    unfold IsWitness
    apply Hand.ext
    intro i
    exact congrFun (List.ofFn_inj.mp hlists) i

theorem iff_scan (c : Hand n) : Meldable c ↔ (scanHand c).isOk := by
  rw [meldable_iff_listMeldable, iff_scanList]
  rfl

end Mahjong.Hand.Meldable.ScanNew
