import NinegatesFormalization.Basic

namespace Mahjong.Hand

namespace Meldable

structure StepPlacement where
  tripNum : ℕ
  seqNum : ℕ
deriving DecidableEq, Repr

abbrev ScanState := ℕ × ℕ -- i-1, i-2

inductive ScanFailure where
  | failEarly
  | failFinally

abbrev ScanM := StateT ScanState (WriterT (List StepPlacement) (Except ScanFailure))

def scanStep (x : ℕ) : ScanM Unit := do
  let s ← get
  unless s.1 + s.2 ≤ x do
    throw .failEarly
  let rem := x - (s.1 + s.2)
  let p : StepPlacement := ⟨rem / 3, rem % 3⟩
  tell [p]
  set (p.seqNum, s.1)

private def finish : ScanM Unit := do
  unless (← get) = (0, 0) do throw .failFinally

def scanList (xs : List ℕ) : ScanM Unit := do
  xs.forM scanStep
  finish

variable {n : ℕ}

namespace Placement

def ofSteps (steps : List StepPlacement) : Placement n where
  tripNum i := (steps.getD i.val ⟨0, 0⟩).tripNum
  seqNum i := (steps.getD i.val ⟨0, 0⟩).seqNum

@[simp]
lemma tripNum_ofSteps (steps : List StepPlacement) (i : Fin (3 * n)) :
    (ofSteps steps : Placement n).tripNum i = (steps.getD i.val ⟨0, 0⟩).tripNum := rfl

@[simp]
lemma seqNum_ofSteps (steps : List StepPlacement) (i : Fin (3 * n - 2)) :
    (ofSteps steps : Placement n).seqNum i = (steps.getD i.val ⟨0, 0⟩).seqNum := rfl

end Placement

def scanHand (c : Hand n) := scanList (List.ofFn fun i ↦ count i c) (0, 0)

private lemma pure_run (a : α) (s : ScanState) :
    ((pure a : ScanM α) s).run = .ok ((a, s), []) := rfl

@[local grind =]
private lemma get_run (s : ScanState) :
    ((get : ScanM ScanState) s).run = .ok ((s, s), []) := rfl

@[local grind =]
private lemma throw_run (e : ScanFailure) (s : ScanState) :
    ((throw e : ScanM Unit) s).run = .error e := rfl

@[local grind =]
private lemma tell_run (w : List StepPlacement) (s : ScanState) :
    ((tell w : ScanM Unit) s).run = .ok (((), s), w) := by
  change (StateT.lift
    (tell w : WriterT (List StepPlacement) (Except ScanFailure) Unit) s).run = _
  simp [StateT.lift]
  rfl

@[local grind =]
private lemma set_run (s s' : ScanState) :
    ((set s' : ScanM Unit) s).run = .ok (((), s'), []) := rfl

@[local grind =]
private lemma bind_run (x : ScanM α) (f : α → ScanM β) (s : ScanState) :
    ((x >>= f) s).run =
      match (x s).run with
      | .error e => .error e
      | .ok ((a, s'), w₁) =>
          match (f a s').run with
          | .error e => .error e
          | .ok ((b, s''), w₂) => .ok ((b, s''), w₁ ++ w₂) := by
  cases h : (x s).run with
  | error e => simp [bind, StateT.bind, Except.bind, h]
  | ok v =>
      rcases v with ⟨⟨a, s'⟩, w₁⟩
      cases h' : (f a s').run <;>
        simp [bind, StateT.bind, Except.bind, h, h']

private lemma scanStep_eq (x : ℕ) (s : ScanState) :
    (scanStep x s).run =
      if s.1 + s.2 ≤ x then
        .ok (((), ((x - (s.1 + s.2)) % 3, s.1)),
          [⟨(x - (s.1 + s.2)) / 3, (x - (s.1 + s.2)) % 3⟩])
      else
        .error .failEarly := by
  unfold scanStep
  grind

private lemma finish_run (s : ScanState) :
    (finish s).run =
      if s = (0, 0) then Except.ok (((), s), []) else Except.error .failFinally := by
  unfold finish
  grind [pure_run]

private def stepAt (steps : List StepPlacement) (i : ℕ) : StepPlacement :=
  steps.getD i ⟨0, 0⟩

private def stateBefore (s : ScanState) (steps : List StepPlacement) (i : ℕ) :
    ScanState :=
  if i = 0 then s else
    ((stepAt steps (i - 1)).seqNum,
      if i = 1 then s.1 else (stepAt steps (i - 2)).seqNum)

private lemma stateBefore_cons_succ (s : ScanState) (p : StepPlacement)
    (steps : List StepPlacement) (i : ℕ) :
    stateBefore s (p :: steps) (i + 1) =
      stateBefore (p.seqNum, s.1) steps i := by
  cases i with
  | zero => simp [stateBefore, stepAt]
  | succ i => cases i <;> simp [stateBefore, stepAt]

private theorem facts_of_scanSteps_eq_ok (xs : List ℕ) (s s' : ScanState)
    (steps : List StepPlacement)
    (h : (((xs.forM scanStep) s).run = .ok (((), s'), steps))) :
    steps.length = xs.length ∧
      (∀ i, i < xs.length →
        xs.getD i 0 =
          let before := stateBefore s steps i
          let p := stepAt steps i
          before.1 + before.2 + 3 * p.tripNum + p.seqNum) ∧
      s' = stateBefore s steps steps.length := by
  induction xs generalizing s s' steps with
  | nil =>
      cases steps with
      | nil =>
          have hs : s = s' := by simpa [pure_run] using h
          subst s'
          simp [stateBefore]
      | cons p ps => simp [pure_run] at h
  | cons x xs ih =>
      cases steps with
      | nil =>
          by_cases hle : s.1 + s.2 ≤ x
          · simp only [List.forM, bind_run, scanStep_eq, if_pos hle] at h
            cases htail :
                ((xs.forM scanStep) ((x - (s.1 + s.2)) % 3, s.1)).run <;>
              rw [htail] at h <;> simp at h
          · simp [bind_run, scanStep_eq, hle] at h
      | cons p ps =>
          by_cases hle : s.1 + s.2 ≤ x
          · simp only [List.forM, bind_run, scanStep_eq, if_pos hle] at h
            cases htail :
                ((xs.forM scanStep) ((x - (s.1 + s.2)) % 3, s.1)).run with
            | error e => rw [htail] at h; simp at h
            | ok out =>
                rcases out with ⟨⟨u, tailState⟩, tailSteps⟩
                rw [htail] at h
                simp only at h
                rcases h with ⟨rfl, rfl, rfl, rfl⟩
                rcases ih _ _ _ htail with ⟨hlen, hlocal, hstate⟩
                refine ⟨by simp [hlen], ?_, ?_⟩
                · intro i hi
                  cases i with
                  | zero =>
                      have hdiv := Nat.mod_add_div (x - (s.1 + s.2)) 3
                      simp [stateBefore, stepAt]
                      omega
                  | succ i =>
                      have hi' : i < xs.length := by simpa using hi
                      have htailLocal := hlocal i hi'
                      simpa [stateBefore_cons_succ, stepAt] using htailLocal
                · rw [hstate]
                  simpa using (stateBefore_cons_succ s
                    ⟨(x - (s.1 + s.2)) / 3, (x - (s.1 + s.2)) % 3⟩
                    tailSteps tailSteps.length).symm
          · simp [bind_run, scanStep_eq, hle] at h

namespace Placement

private def seqNumAt (p : Placement n) (i : ℕ) : ℕ :=
  if h : i < 3 * n - 2 then p.seqNum ⟨i, h⟩ else 0

private def pendingSeqs (p : Placement n) (i : ℕ) : ScanState :=
  (if 0 < i then p.seqNumAt (i - 1) else 0,
    if 1 < i then p.seqNumAt (i - 2) else 0)

private def scanStateBefore (p : Placement n) (i : ℕ) : ScanState :=
  ((p.pendingSeqs i).1 % 3, (p.pendingSeqs i).2 % 3)

private lemma sum_seq_offset (p : Placement n) (k : Fin (3 * n))
    (d : ℕ) (hd : d ≤ 2) :
    (∑ j, p.seqNum j *
      (if k = (⟨j.val + d, by omega⟩ : Fin (3 * n)) then 1 else 0)) =
      if d ≤ k.val then p.seqNumAt (k.val - d) else 0 := by
  by_cases hdk : d ≤ k.val
  · rw [if_pos hdk]
    unfold seqNumAt
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

private lemma count_toHand_local (p : Placement n) (k : Fin (3 * n)) :
    count k p.toHand =
      (p.pendingSeqs k.val).1 + (p.pendingSeqs k.val).2 +
        3 * p.tripNum k + p.seqNumAt k.val := by
  have htrip :
      (∑ i, p.tripNum i • count k (Hand.triplet i)) = 3 * p.tripNum k := by
    simp [Hand.triplet, Hand.single, mul_comm]
  have h0 :
      (∑ j, if k = (⟨j.val, by omega⟩ : Fin (3 * n)) then p.seqNum j else 0) =
        p.seqNumAt k.val := by
    simpa using sum_seq_offset p k 0 (by omega)
  have h1 :
      (∑ j, if k = (⟨j.val + 1, by omega⟩ : Fin (3 * n)) then p.seqNum j else 0) =
        if 0 < k.val then p.seqNumAt (k.val - 1) else 0 := by
    have h := sum_seq_offset p k 1 (by omega)
    by_cases hk : 1 ≤ k.val
    · have hk' : 0 < k.val := by omega
      simpa [hk, hk'] using h
    · have hk' : ¬ 0 < k.val := by omega
      simpa [hk, hk'] using h
  have h2 :
      (∑ j, if k = (⟨j.val + 2, by omega⟩ : Fin (3 * n)) then p.seqNum j else 0) =
        if 1 < k.val then p.seqNumAt (k.val - 2) else 0 := by
    have h := sum_seq_offset p k 2 (by omega)
    by_cases hk : 2 ≤ k.val
    · have hk' : 1 < k.val := by omega
      simpa [hk, hk'] using h
    · have hk' : ¬ 1 < k.val := by omega
      simpa [hk, hk'] using h
  rw [Placement.count_toHand, htrip]
  simp only [Hand.sequence, Hand.single, count_apply, add_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [h0, h1, h2]
  simp only [pendingSeqs]
  omega

private lemma scanStateBefore_succ (p : Placement n) (i : ℕ) :
    p.scanStateBefore (i + 1) = (p.seqNumAt i % 3, (p.scanStateBefore i).1) := by
  cases i <;> simp [scanStateBefore, pendingSeqs]

private lemma scanStateBefore_zero (p : Placement n) :
    p.scanStateBefore 0 = (0, 0) := by
  simp [scanStateBefore, pendingSeqs]

private lemma scanStateBefore_end (p : Placement n) :
    p.scanStateBefore (3 * n) = (0, 0) := by
  by_cases hn : n = 0
  · subst n
    simp [scanStateBefore, pendingSeqs]
  · have hnpos : 0 < n := by omega
    have hlast : ¬3 * n - 1 < 3 * n - 2 := by omega
    simp [scanStateBefore, pendingSeqs, seqNumAt, hnpos, hlast]

end Placement

private lemma scanStep_witness (p : Placement n) (i : ℕ) (hi : i < 3 * n) :
    ∃ q, (scanStep (p.toHand.count ⟨i, hi⟩) (p.scanStateBefore i)).run =
      .ok (((), p.scanStateBefore (i + 1)), [q]) := by
  let a := (p.pendingSeqs i).1
  let b := (p.pendingSeqs i).2
  let z := p.seqNumAt i
  let t := p.tripNum ⟨i, hi⟩
  have hcount := p.count_toHand_local (⟨i, hi⟩ : Fin (3 * n))
  change count ⟨i, hi⟩ p.toHand = a + b + 3 * t + z at hcount
  have ha := Nat.mod_add_div a 3
  have hb := Nat.mod_add_div b 3
  have hz := Nat.mod_add_div z 3
  have hle : a % 3 + b % 3 ≤ count ⟨i, hi⟩ p.toHand := by omega
  let rem := count ⟨i, hi⟩ p.toHand - (a % 3 + b % 3)
  have hrem :
      rem = 3 * (a / 3 + b / 3 + t + z / 3) + z % 3 := by
    dsimp only [rem]
    omega
  let q : StepPlacement := ⟨rem / 3, rem % 3⟩
  let r := 3 * (a / 3 + b / 3 + t + z / 3) + z % 3
  have hrmod : r % 3 = z % 3 := by
    simp [r, Nat.add_mod]
  have hq : q = (⟨r / 3, z % 3⟩ : StepPlacement) := by
    change (⟨rem / 3, rem % 3⟩ : StepPlacement) = _
    rw [hrem, show 3 * (a / 3 + b / 3 + t + z / 3) + z % 3 = r by rfl,
      hrmod]
  refine ⟨q, ?_⟩
  rw [scanStep_eq, if_pos]
  · rw [show p.scanStateBefore i = (a % 3, b % 3) by rfl,
      show count ⟨i, hi⟩ p.toHand - (a % 3 + b % 3) = rem by rfl, hrem,
      show 3 * (a / 3 + b / 3 + t + z / 3) + z % 3 = r by rfl,
      hrmod, Placement.scanStateBefore_succ, hq]
    simp [z, a, Placement.scanStateBefore]
  · simpa [Placement.scanStateBefore, a, b] using hle

private theorem scan_from_witness (p : Placement n) (i : ℕ) (hi : i ≤ 3 * n) :
    ∃ steps,
      ((((List.ofFn fun k ↦ count k p.toHand).drop i).forM scanStep)
          (p.scanStateBefore i)).run =
        .ok (((), p.scanStateBefore (3 * n)), steps) := by
  induction hi using Nat.decreasingInduction with
  | self =>
      refine ⟨[], ?_⟩
      rw [List.drop_of_length_le (by simp)]
      change ((pure () : ScanM Unit) (p.scanStateBefore (3 * n))).run = _
      exact pure_run () _
  | of_succ i hi ih =>
      have hlen : (List.ofFn fun k ↦ count k p.toHand).length = 3 * n := by simp
      rw [List.drop_eq_getElem_cons (show i <
        (List.ofFn fun k ↦ count k p.toHand).length by simpa [hlen])]
      have hhead :
          (List.ofFn fun k ↦ count k p.toHand)[i] =
            count (⟨i, by omega⟩ : Fin (3 * n)) p.toHand := by
        simp
      simp only [List.forM, bind_run]
      rw [hhead]
      rcases scanStep_witness p i (by omega) with ⟨q, hq⟩
      rw [hq]
      simp only
      rcases ih with ⟨steps, hsteps⟩
      rw [hsteps]
      exact ⟨q :: steps, rfl⟩

private theorem scanHand_isOk_of_isWitness {p : Placement n} {c : Hand n}
    (hp : IsWitness p c) : (scanHand c).isOk := by
  unfold IsWitness at hp
  subst c
  rcases scan_from_witness p 0 (by omega) with ⟨steps, hsteps⟩
  simp only [List.drop_zero] at hsteps
  rw [Placement.scanStateBefore_end] at hsteps
  rw [Placement.scanStateBefore_zero] at hsteps
  unfold scanHand
  change (scanList (List.ofFn fun i ↦ count i p.toHand) (0, 0)).run.isOk
  unfold scanList
  rw [bind_run, hsteps]
  simp only
  rw [finish_run]
  rfl

private theorem isWitness_of_scanHand_eq_ok (c : Hand n)
    {s : ScanState} (steps : List StepPlacement)
    (h : scanHand c = .ok (((), s), steps)) :
    IsWitness (Placement.ofSteps steps) c := by
  unfold scanHand at h
  change (scanList (List.ofFn fun i ↦ count i c) (0, 0)).run =
    .ok (((), s), steps) at h
  unfold scanList at h
  rw [bind_run] at h
  cases hrun :
      (((List.ofFn fun i ↦ count i c).forM scanStep) (0, 0)).run with
  | error e => simp only [hrun] at h; contradiction
  | ok out =>
      rcases out with ⟨⟨u, finalState⟩, scannedSteps⟩
      cases u
      simp only [hrun] at h
      rw [finish_run] at h
      by_cases hfinal : finalState = (0, 0)
      · subst finalState
        rw [if_pos rfl] at h
        simp only [List.append_nil] at h
        change Except.ok (((), (0, 0)), scannedSteps) =
          Except.ok (((), s), steps) at h
        have hout := Except.ok.inj h
        have hs : (0, 0) = s := congrArg (fun out ↦ out.1.2) hout
        have hsteps : scannedSteps = steps := congrArg Prod.snd hout
        subst s
        subst steps
        rcases facts_of_scanSteps_eq_ok _ _ _ _ hrun with
          ⟨hlen, hlocal, hstate⟩
        have hseq : ∀ i, i < 3 * n →
            (Placement.ofSteps scannedSteps : Placement n).seqNumAt i =
              (stepAt scannedSteps i).seqNum := by
          intro i hi
          unfold Placement.seqNumAt
          split
          next hibound => simp [stepAt]
          next hibound =>
            have hn : 1 ≤ n := by omega
            have htail :
                ((stepAt scannedSteps (3 * n - 1)).seqNum,
                  (stepAt scannedSteps (3 * n - 2)).seqNum) = (0, 0) := by
              have hstate' := hstate.symm
              rw [hlen] at hstate'
              simpa [stateBefore, show 3 * n ≠ 0 by omega,
                show 3 * n ≠ 1 by omega] using hstate'
            have hlast : (stepAt scannedSteps (3 * n - 1)).seqNum = 0 :=
              congrArg Prod.fst htail
            have hpenult : (stepAt scannedSteps (3 * n - 2)).seqNum = 0 :=
              congrArg Prod.snd htail
            have hi' : i = 3 * n - 2 ∨ i = 3 * n - 1 := by omega
            rcases hi' with rfl | rfl
            · exact hpenult.symm
            · exact hlast.symm
        unfold IsWitness
        apply Hand.ext
        intro k
        have hprev :
            (Placement.ofSteps scannedSteps : Placement n).pendingSeqs k.val =
              stateBefore (0, 0) scannedSteps k.val := by
          by_cases hk0 : k.val = 0
          · simp [hk0, Placement.pendingSeqs, stateBefore]
          by_cases hk1 : k.val = 1
          · have hs0 := hseq 0 (by omega)
            simp [hk1, Placement.pendingSeqs, stateBefore, hs0]
          · have hkgt : 1 < k.val := by omega
            have hs1 := hseq (k.val - 1) (by omega)
            have hs2 := hseq (k.val - 2) (by omega)
            simp [Placement.pendingSeqs, stateBefore, hk0, hk1, hkgt, hs1, hs2]
        change count k (Placement.ofSteps scannedSteps : Placement n).toHand =
          count k c
        rw [Placement.count_toHand_local, hprev, hseq k.val k.isLt]
        have hkLocal := hlocal k.val (by simp)
        simpa [stepAt] using hkLocal.symm
      · simp [hfinal] at h

theorem iff_scan {n : ℕ} (c : Hand n) : Meldable c ↔ (scanHand c).isOk := by
  constructor
  · rintro ⟨p, hp⟩
    exact scanHand_isOk_of_isWitness hp
  · intro hok
    cases hscan : scanHand c with
    | error e =>
        rw [hscan] at hok
        change false = true at hok
        contradiction
    | ok out =>
        rcases out with ⟨⟨u, s⟩, steps⟩
        cases u
        exact ⟨Placement.ofSteps steps,
          isWitness_of_scanHand_eq_ok c steps hscan⟩

end Meldable

end Mahjong.Hand
