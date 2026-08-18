import NinegatesFormalization.Basic
import Std.Tactic.Do

namespace Mahjong.Hand.Meldable.ScanNew2

open Std.Internal.Do

abbrev ScanState := ℕ × ℕ

inductive Failure where
  | failEarly
  | failFinally
deriving DecidableEq, Repr

abbrev ScanM := EStateM Failure ScanState

private def nextState (x : ℕ) (s : ScanState) : ScanState :=
  ((x - (s.1 + s.2)) % 3, s.1)

def scanStep (x : ℕ) : ScanM Unit := do
  let s ← get
  unless s.1 + s.2 ≤ x do
    throw .failEarly
  set (nextState x s)

private def finish : ScanM Unit := do
  unless (← get) = (0, 0) do
    throw .failFinally

def scan : List ℕ → ScanM Unit
  | [] => finish
  | x :: xs => do
      scanStep x
      scan xs

abbrev ScanResult := EStateM.Result Failure ScanState Unit

namespace ScanResult

@[grind =]
def isOk : ScanResult → Bool
  | .ok _ _ => true
  | .error _ _ => false

end ScanResult

def scanList (xs : List ℕ) : ScanResult :=
  (scan xs).run (0, 0)

def scanHand (c : Hand n) : ScanResult :=
  scanList (List.ofFn fun i ↦ c i)

private def Accepts : ScanState → List ℕ → Prop
  | s, [] => s = (0, 0)
  | s, x :: xs => s.1 + s.2 ≤ x ∧ Accepts (nextState x s) xs

@[local grind =]
private theorem accepts_nil (s : ScanState) :
    Accepts s [] = (s = (0, 0)) := rfl

@[local grind =]
private theorem accepts_cons (s : ScanState) (x : ℕ) (xs : List ℕ) :
    Accepts s (x :: xs) =
      (s.1 + s.2 ≤ x ∧ Accepts (nextState x s) xs) := rfl

@[spec]
private theorem scanStep_spec (x : ℕ) (initial : ScanState) :
    ⦃ fun s => s = initial ⦄
      scanStep x
    ⦃ (fun _ s => initial.1 + initial.2 ≤ x ∧ s = nextState x initial);
      (fun e s => e = .failEarly ∧
        ¬initial.1 + initial.2 ≤ x ∧ s = initial) ⦄ := by
  vcgen [scanStep] with finish

@[spec]
private theorem finish_spec (initial : ScanState) :
    ⦃ fun s => s = initial ⦄
      finish
    ⦃ (fun _ s => initial = (0, 0) ∧ s = initial);
      (fun e s => e = .failFinally ∧ initial ≠ (0, 0) ∧ s = initial) ⦄ := by
  vcgen [finish] with finish

@[spec]
private theorem scan_spec (xs : List ℕ) (initial : ScanState) :
    ⦃ fun s => s = initial ⦄
      scan xs
    ⦃ (fun _ final => Accepts initial xs ∧ final = (0, 0));
      (fun _ _ => ¬Accepts initial xs) ⦄ := by
  induction xs generalizing initial <;>
    vcgen [scan, *] with finish

private theorem accepts_iff_scanList (xs : List ℕ) :
    Accepts (0, 0) xs ↔ (scanList xs).isOk := by
  refine EStateM.of_wp_run_eq (x := scanList xs) (prog := scan xs)
    (s := (0, 0)) rfl
    (fun r => Accepts (0, 0) xs ↔ ScanResult.isOk r = true) ?_
  vcgen [scan_spec] with finish

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

private lemma toHand_apply_pending (p : Placement n) (k : Fin (3 * n)) :
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
  calc
    p.toHand k =
        (∑ i, (p.tripNum i • Hand.triplet i) k) +
          ∑ j, (p.seqNum j • Hand.sequence j) k :=
      Placement.toHand_apply p k
    _ = 3 * p.tripNum k +
        ∑ j, (p.seqNum j • Hand.sequence j) k := by simp only [htrip]
    _ = (pending p k.val).1 + (pending p k.val).2 +
        3 * p.tripNum k + seqAt p k.val := by
      simp only [Hand.sequence, Hand.single, Hand.mk_apply, smul_apply,
        add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        mul_ite, mul_one, mul_zero]
      simp only [h0, h1, h2, pending]
      omega

private def seqQuotAt (p : Placement n) (i : ℕ) : ℕ :=
  seqAt p i / 3

private def normalizePlacement (p : Placement n) : Placement n where
  tripNum k :=
    p.tripNum k + seqQuotAt p k.val +
      (if 0 < k.val then seqQuotAt p (k.val - 1) else 0) +
      (if 1 < k.val then seqQuotAt p (k.val - 2) else 0)
  seqNum i := p.seqNum i % 3

private lemma seqAt_normalizePlacement (p : Placement n) (i : ℕ) :
    seqAt (normalizePlacement p) i = seqAt p i % 3 := by
  unfold seqAt
  split <;> simp [normalizePlacement]

private lemma normalizePlacement_seqNum_lt (p : Placement n)
    (i : Fin (3 * n - 2)) :
    (normalizePlacement p).seqNum i < 3 := by
  exact Nat.mod_lt _ (by omega)

private theorem normalizePlacement_toHand (p : Placement n) :
    (normalizePlacement p).toHand = p.toHand := by
  apply Hand.ext
  intro k
  rw [toHand_apply_pending, toHand_apply_pending]
  simp only [pending]
  simp only [seqAt_normalizePlacement]
  simp only [normalizePlacement, seqQuotAt]
  split_ifs
  all_goals omega

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

private theorem accepts_toHand_of_seqNum_lt (p : Placement n)
    (hseq : ∀ i, p.seqNum i < 3) :
    Accepts (0, 0) (List.ofFn fun k ↦ p.toHand k) := by
  have hseqAt (i : ℕ) : seqAt p i < 3 := by
    unfold seqAt
    split
    · exact hseq _
    · omega
  have hstep (i : ℕ) (hi : i < 3 * n) :
      nextState (p.toHand ⟨i, hi⟩) (pending p i) = pending p (i + 1) := by
    rw [toHand_apply_pending, pending_succ]
    unfold nextState
    have hlt := hseqAt i
    simp only [Prod.mk.injEq]
    constructor
    · have hsub :
          ((pending p i).1 + (pending p i).2 +
            3 * p.tripNum ⟨i, hi⟩ + seqAt p i) -
              ((pending p i).1 + (pending p i).2) =
            3 * p.tripNum ⟨i, hi⟩ + seqAt p i := by omega
      rw [hsub]
      omega
    · trivial
  have aux (i : ℕ) (hi : i ≤ 3 * n) :
      Accepts (pending p i) ((List.ofFn fun k ↦ p.toHand k).drop i) := by
    induction hi using Nat.decreasingInduction with
    | self =>
        rw [List.drop_of_length_le (by simp)]
        exact (accepts_nil _).mpr (pending_end p)
    | of_succ i hi ih =>
        have hicounts : i < (List.ofFn fun k ↦ p.toHand k).length := by
          simp
          omega
        rw [List.drop_eq_getElem_cons hicounts, List.getElem_ofFn]
        apply (accepts_cons _ _ _).mpr
        constructor
        · have hlocal := toHand_apply_pending p ⟨i, by omega⟩
          simp at hlocal
          omega
        · rw [hstep i (by omega)]
          exact ih
  simpa only [pending_zero, List.drop_zero] using aux 0 (by omega)

private theorem accepts_toHand (p : Placement n) :
    Accepts (0, 0) (List.ofFn fun k ↦ p.toHand k) := by
  have h := accepts_toHand_of_seqNum_lt (normalizePlacement p)
    (normalizePlacement_seqNum_lt p)
  simpa only [normalizePlacement_toHand] using h

private def stateAt (xs : List ℕ) (i : ℕ) : ScanState :=
  (xs.take i).foldl (fun s x ↦ nextState x s) (0, 0)

private lemma stateAt_zero (xs : List ℕ) : stateAt xs 0 = (0, 0) := by
  rfl

private lemma stateAt_succ (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    stateAt xs (i + 1) = nextState xs[i] (stateAt xs i) := by
  unfold stateAt
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem accepts_stateAt_drop {xs : List ℕ} (h : Accepts (0, 0) xs)
    (i : ℕ) (hi : i ≤ xs.length) :
    Accepts (stateAt xs i) (xs.drop i) := by
  induction i with
  | zero =>
      simpa only [stateAt_zero, List.drop_zero] using h
  | succ i ih =>
      have hilength : i < xs.length := by omega
      have hprev := ih (by omega)
      rw [List.drop_eq_getElem_cons hilength] at hprev
      have hnext := (accepts_cons _ _ _).mp hprev |>.2
      simpa only [stateAt_succ xs i hilength] using hnext

private def residual (c : Hand n) (i : Fin (3 * n)) : ℕ :=
  let s := stateAt (List.ofFn fun k ↦ c k) i.val
  c i - (s.1 + s.2)

-- if this has been defined, why do we need a monadic scan?
private def canonicalPlacement (c : Hand n) : Placement n where
  tripNum i := residual c i / 3
  seqNum i := residual c ⟨i.val, by omega⟩ % 3

private theorem canonicalPlacement_toHand (c : Hand n)
    (h : Accepts (0, 0) (List.ofFn fun i ↦ c i)) :
    (canonicalPlacement c).toHand = c := by
  have hhead (i : ℕ) (hi : i < 3 * n) :
      (stateAt (List.ofFn fun k ↦ c k) i).1 +
          (stateAt (List.ofFn fun k ↦ c k) i).2 ≤ c ⟨i, hi⟩ := by
    have ha := accepts_stateAt_drop h i (by simp; omega)
    have hilength : i < (List.ofFn fun k ↦ c k).length := by simpa
    rw [List.drop_eq_getElem_cons hilength, List.getElem_ofFn] at ha
    exact (accepts_cons _ _ _).mp ha |>.1
  have hstateSucc (i : ℕ) (hi : i < 3 * n) :
      stateAt (List.ofFn fun k ↦ c k) (i + 1) =
        (residual c ⟨i, hi⟩ % 3,
          (stateAt (List.ofFn fun k ↦ c k) i).1) := by
    rw [stateAt_succ _ i (by simpa)]
    simp only [List.getElem_ofFn]
    rfl
  have hend : stateAt (List.ofFn fun k ↦ c k) (3 * n) = (0, 0) := by
    have ha := accepts_stateAt_drop h (3 * n) (by simp)
    rw [List.drop_of_length_le (by simp)] at ha
    exact (accepts_nil _).mp ha
  have hseqAt (i : ℕ) (hi : i < 3 * n) :
      seqAt (canonicalPlacement c) i = residual c ⟨i, hi⟩ % 3 := by
    unfold seqAt
    split
    · simp [canonicalPlacement]
    next hbound =>
      have hiCases : i + 1 = 3 * n ∨ i + 2 = 3 * n := by omega
      rcases hiCases with hiLast | hiPenultimate
      · have hs := congrArg Prod.fst (hstateSucc i hi)
        rw [hiLast, hend] at hs
        simpa using hs
      · have hs1 := congrArg Prod.fst (hstateSucc i hi)
        have hs2 := congrArg Prod.snd (hstateSucc (i + 1) (by omega))
        rw [hiPenultimate, hend] at hs2
        simp only at hs1 hs2
        omega
  have hpending (i : ℕ) (hi : i ≤ 3 * n) :
      pending (canonicalPlacement c) i =
        stateAt (List.ofFn fun k ↦ c k) i := by
    induction i with
    | zero =>
        rw [pending_zero, stateAt_zero]
    | succ i ih =>
        rw [pending_succ, ih (by omega), hseqAt i (by omega),
          hstateSucc i (by omega)]
  apply Hand.ext
  intro k
  rw [toHand_apply_pending, hpending k.val (by omega),
    hseqAt k.val k.isLt]
  simp only [canonicalPlacement]
  have hle :
      (stateAt (List.ofFn fun i ↦ c i) k.val).1 +
          (stateAt (List.ofFn fun i ↦ c i) k.val).2 ≤ c k := by
    simpa using hhead k.val k.isLt
  have hmod := Nat.mod_add_div (residual c k) 3
  unfold residual at hmod ⊢
  simp at hmod ⊢
  omega

private theorem meldable_iff_accepts (c : Hand n) :
    Meldable c ↔ Accepts (0, 0) (List.ofFn fun i ↦ c i) := by
  constructor
  · rintro ⟨p, hp⟩
    unfold IsWitness at hp
    subst c
    exact accepts_toHand p
  · intro h
    exact ⟨canonicalPlacement c, canonicalPlacement_toHand c h⟩

theorem iff_scan (c : Hand n) : Meldable c ↔ (scanHand c).isOk := by
  exact (meldable_iff_accepts c).trans (accepts_iff_scanList _)

end Mahjong.Hand.Meldable.ScanNew2
