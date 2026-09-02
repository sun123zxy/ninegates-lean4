import Ninegates.Model

namespace Ninegates

/-- The one-based weighted sum of the multiplicities in a count vector. -/
def rankSum {n : ℕ} (d : Counts n) : ℕ :=
  ∑ i : Fin n, (i.val + 1) * d i

/--
The two pending run counts used by the canonical scan. Each component is
the least nonnegative residue modulo three.
-/
def ScanState := Fin 3 × Fin 3

/--
Read one multiplicity in the canonical scan. The step fails if the incoming
runs require more tiles than are present at the current rank.
-/
def scanStep (σ : ScanState) (z : ℕ) : Option ScanState :=
  if σ.1.val + σ.2.val ≤ z then
    some
      (σ.2,
        ⟨(z - σ.1.val - σ.2.val) % 3, Nat.mod_lt _ (by decide)⟩)
  else
    none

/-- Scan a count vector from left to right, starting from an arbitrary state. -/
def scan {n : ℕ} (d : Counts n) (σ : ScanState := (0, 0)) :
    Option ScanState :=
  (List.ofFn d).foldlM scanStep σ

/-- A count vector is accepted when its canonical scan succeeds from zero to zero. -/
def ScanAccepts {n : ℕ} (d : Counts n) : Prop :=
  scan d = some (0, 0)

/- A singleton sum over `Fin m`, selected by the natural value of the index. -/
private lemma sum_if_fin_val_eq {m : ℕ} (i : ℕ) (f : Fin m → ℕ) :
    (∑ j : Fin m, if j.val = i then f j else 0) =
      if h : i < m then f ⟨i, h⟩ else 0 := by
  by_cases h : i < m
  · rw [dif_pos h]
    convert Fintype.sum_ite_eq' (⟨i, h⟩ : Fin m) f with j
    · constructor
      · intro hv
        ext
        simp [hv]
      · intro hj
        rw [hj]
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hv : j.val = i
    · exact (h (by simpa [hv] using j.isLt)).elim
    · simp [hv]

/- The weighted contribution of a run is the sum of its three consecutive ranks. -/
private lemma run_weight_sum {n : ℕ} (runs : Fin (n - 2) → ℕ)
    (j : Fin (n - 2)) :
    (∑ i : Fin n,
      (i.val + 1) * (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)) =
        3 * (j.val + 2) * runs j := by
  have hj0 : j.val < n := by omega
  have hj1 : j.val + 1 < n := by omega
  have hj2 : j.val + 2 < n := by omega
  calc
    (∑ i : Fin n,
      (i.val + 1) * (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0))
        = ∑ i : Fin n,
            ((if i.val = j.val then (i.val + 1) * runs j else 0) +
             (if i.val = j.val + 1 then (i.val + 1) * runs j else 0) +
             (if i.val = j.val + 2 then (i.val + 1) * runs j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h0 : i.val = j.val <;>
          by_cases h1 : i.val = j.val + 1 <;>
          by_cases h2 : i.val = j.val + 2 <;>
          simp [h0, h1, h2]; omega
    _ = (∑ i : Fin n, if i.val = j.val then (i.val + 1) * runs j else 0) +
        (∑ i : Fin n, if i.val = j.val + 1 then (i.val + 1) * runs j else 0) +
        (∑ i : Fin n, if i.val = j.val + 2 then (i.val + 1) * runs j else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = (j.val + 1) * runs j + (j.val + 2) * runs j +
        (j.val + 3) * runs j := by
          rw [sum_if_fin_val_eq j.val (fun i : Fin n => (i.val + 1) * runs j),
            sum_if_fin_val_eq (j.val + 1) (fun i : Fin n => (i.val + 1) * runs j),
            sum_if_fin_val_eq (j.val + 2) (fun i : Fin n => (i.val + 1) * runs j)]
          simp [hj0, hj1, hj2]
    _ = 3 * (j.val + 2) * runs j := by ring

/- If each term is zero modulo three, then so is the finite sum. -/
private lemma sum_modEq_zero {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (h : ∀ i, Nat.ModEq 3 (f i) 0) :
    Nat.ModEq 3 (∑ i, f i) 0 := by
  classical
  exact Finset.induction_on (Finset.univ : Finset ι)
    (by rfl)
    (by
      intro a s has ih
      rw [Finset.sum_insert has]
      exact Nat.ModEq.add (h a) ih)

/-- Every meldable count vector has rank sum divisible by three. -/
lemma meldable_rankSum_mod {n : ℕ} (d : Counts n) (hd : Meldable d) :
    Nat.ModEq 3 (rankSum d) 0 := by
  rcases hd with ⟨triplets, runs, hd⟩
  unfold rankSum
  have hrewrite :
      (∑ i : Fin n, (i.val + 1) * d i) =
        (∑ i : Fin n, (i.val + 1) * (3 * triplets i)) +
          (∑ j : Fin (n - 2), 3 * (j.val + 2) * runs j) := by
    calc
      (∑ i : Fin n, (i.val + 1) * d i)
          = ∑ i : Fin n,
              (i.val + 1) *
                (3 * triplets i +
                  ∑ j : Fin (n - 2),
                    if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hd i]
      _ = (∑ i : Fin n, (i.val + 1) * (3 * triplets i)) +
            ∑ i : Fin n,
              (i.val + 1) *
                (∑ j : Fin (n - 2),
                  if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
              simp [Nat.mul_add, Finset.sum_add_distrib]
      _ = (∑ i : Fin n, (i.val + 1) * (3 * triplets i)) +
            ∑ i : Fin n,
              ∑ j : Fin (n - 2),
                (i.val + 1) *
                  (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
              simp [Finset.mul_sum]
      _ = (∑ i : Fin n, (i.val + 1) * (3 * triplets i)) +
            ∑ j : Fin (n - 2),
              ∑ i : Fin n,
                (i.val + 1) *
                  (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
              rw [Finset.sum_comm]
      _ = (∑ i : Fin n, (i.val + 1) * (3 * triplets i)) +
            ∑ j : Fin (n - 2), 3 * (j.val + 2) * runs j := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              exact run_weight_sum runs j
  rw [hrewrite]
  have hTriplets : Nat.ModEq 3 (∑ i : Fin n, (i.val + 1) * (3 * triplets i)) 0 := by
    apply sum_modEq_zero
    intro i
    apply Nat.modEq_zero_iff_dvd.mpr
    refine ⟨(i.val + 1) * triplets i, ?_⟩
    ring
  have hRuns : Nat.ModEq 3 (∑ j : Fin (n - 2), 3 * (j.val + 2) * runs j) 0 := by
    apply sum_modEq_zero
    intro j
    apply Nat.modEq_zero_iff_dvd.mpr
    refine ⟨(j.val + 2) * runs j, ?_⟩
    ring
  simpa using Nat.ModEq.add hTriplets hRuns

/- Rank sum is additive for pointwise addition of count vectors. -/
private lemma rankSum_add {n : ℕ} (a b : Counts n) :
    rankSum (fun i => a i + b i) = rankSum a + rankSum b := by
  simp [rankSum, Nat.mul_add, Finset.sum_add_distrib]

/- The rank sum of two copies of one basis vector is twice its one-based rank. -/
private lemma rankSum_two_basis {n : ℕ} (p : Fin n) :
    rankSum (fun i : Fin n => 2 * basis p i) = 2 * (p.val + 1) := by
  unfold rankSum basis
  calc
    (∑ i : Fin n, (i.val + 1) * (2 * if i = p then 1 else 0))
        = ∑ i : Fin n, if i = p then 2 * (p.val + 1) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i = p
          · subst h
            simp [mul_comm]
          · simp [h]
    _ = 2 * (p.val + 1) := by
          rw [Fintype.sum_ite_eq']

/- The rank sum of one basis vector is its one-based rank. -/
private lemma rankSum_basis {n : ℕ} (p : Fin n) :
    rankSum (basis p) = p.val + 1 := by
  unfold rankSum basis
  calc
    (∑ i : Fin n, (i.val + 1) * (if i = p then 1 else 0))
        = ∑ i : Fin n, if i = p then p.val + 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i = p <;> simp [h]
    _ = p.val + 1 := by
          rw [Fintype.sum_ite_eq']

/- Adding a basis vector increases the rank sum by the corresponding rank. -/
private lemma rankSum_add_basis {n : ℕ} (c : Counts n) (x : Fin n) :
    rankSum (fun i => c i + basis x i) = rankSum c + (x.val + 1) := by
  rw [rankSum_add, rankSum_basis]

/- Removing a pair lowers the rank sum by twice the pair rank. -/
private lemma removePair_rankSum_add_pair {n : ℕ} (w : Counts n) (p : Fin n)
    (hp : 2 ≤ w p) :
    rankSum (removePair w p) + 2 * (p.val + 1) = rankSum w := by
  have hpoint : ∀ i : Fin n, removePair w p i + 2 * basis p i = w i := by
    intro i
    by_cases h : i = p
    · subst h
      simp [removePair, basis, Nat.sub_add_cancel hp]
    · simp [removePair, basis, h]
  calc
    rankSum (removePair w p) + 2 * (p.val + 1)
        = rankSum (removePair w p) + rankSum (fun i : Fin n => 2 * basis p i) := by
          rw [rankSum_two_basis]
    _ = rankSum (fun i : Fin n => removePair w p i + 2 * basis p i) := by
          rw [rankSum_add]
    _ = rankSum w := by
          congr 1
          funext i
          exact hpoint i

/--
If drawing `x` and choosing the pair at `p` leaves a meldable remainder, then
the original rank sum plus the drawn rank is congruent to twice the pair rank.
-/
lemma complete_rankSum_mod {n : ℕ} (c : Counts n) (x p : Fin n)
    (hp : 2 ≤ (fun i ↦ c i + basis x i) p)
    (hMeldable : Meldable (removePair (fun i ↦ c i + basis x i) p)) :
    Nat.ModEq 3 (rankSum c + (x.val + 1)) (2 * (p.val + 1)) := by
  let w : Counts n := fun i => c i + basis x i
  have hrem :
      rankSum (removePair w p) + 2 * (p.val + 1) = rankSum w :=
    removePair_rankSum_add_pair w p hp
  have hw : rankSum w = rankSum c + (x.val + 1) := by
    change rankSum (fun i => c i + basis x i) = rankSum c + (x.val + 1)
    exact rankSum_add_basis c x
  have hEq : rankSum (removePair w p) + 2 * (p.val + 1) =
      rankSum c + (x.val + 1) := by
    rw [hrem, hw]
  have hmod := meldable_rankSum_mod (removePair w p) hMeldable
  have h := Nat.ModEq.add hmod (Nat.ModEq.refl (2 * (p.val + 1)))
  rw [hEq] at h
  simpa using h

/- The normalized run count at a natural index, extended by zero outside bounds. -/
private def scanStartAt {n : ℕ} (starts : Counts n) (k : ℕ) : ℕ :=
  if h : k < n then starts ⟨k, h⟩ else 0

/- Add a head entry to a count vector, using values rather than `Fin.cases`. -/
private def countsCons {n : ℕ} (head : ℕ) (tail : Counts n) : Counts (n + 1) :=
  fun i => if h : i.val = 0 then head else tail ⟨i.val - 1, by omega⟩

/- The first incoming run count at a coordinate, relative to an initial state. -/
private def scanPrev2 {n : ℕ} (σ : ScanState) (starts : Counts n)
    (i : Fin n) : ℕ :=
  if i.val = 0 then σ.1.val else
    if i.val = 1 then σ.2.val else scanStartAt starts (i.val - 2)

/- The second incoming run count at a coordinate, relative to an initial state. -/
private def scanPrev1 {n : ℕ} (σ : ScanState) (starts : Counts n)
    (i : Fin n) : ℕ :=
  if i.val = 0 then σ.2.val else scanStartAt starts (i.val - 1)

/- The first output state component determined by normalized starts. -/
private def scanOut1 {n : ℕ} (σ : ScanState) (starts : Counts n) : ℕ :=
  match n with
  | 0 => σ.1.val
  | 1 => σ.2.val
  | k + 2 => starts ⟨k, by omega⟩

/- The second output state component determined by normalized starts. -/
private def scanOut2 {n : ℕ} (σ : ScanState) (starts : Counts n) : ℕ :=
  match n with
  | 0 => σ.2.val
  | k + 1 => starts ⟨k, by omega⟩

/- Output state after adding one head start agrees with the tail output, first component. -/
private lemma scanOut1_cons {n : ℕ} (σ σ' : ScanState) (starts : Counts n)
    (hσ' : σ'.1.val = σ.2.val) :
    scanOut1 σ (countsCons σ'.2.val starts : Counts (n + 1)) =
      scanOut1 σ' starts := by
  cases n with
  | zero =>
      simp [scanOut1, hσ']
  | succ n =>
      cases n <;> simp [scanOut1, countsCons]

/- Output state after adding one head start agrees with the tail output, second component. -/
private lemma scanOut2_cons {n : ℕ} (σ σ' : ScanState) (starts : Counts n) :
    scanOut2 σ (countsCons σ'.2.val starts : Counts (n + 1)) =
      scanOut2 σ' starts := by
  cases n <;> simp [scanOut2, countsCons]

/- Removing the head of the starts shifts the first output component. -/
private lemma scanOut1_tail {n : ℕ} (σ : ScanState) (starts : Counts (n + 1))
    (h0 : starts 0 < 3) :
    scanOut1 ((σ.2, ⟨starts 0, h0⟩) : ScanState) (fun i : Fin n => starts i.succ) =
      scanOut1 σ starts := by
  cases n with
  | zero =>
      simp [scanOut1]
  | succ n =>
      cases n <;> simp [scanOut1]

/- Removing the head of the starts shifts the second output component. -/
private lemma scanOut2_tail {n : ℕ} (σ : ScanState) (starts : Counts (n + 1))
    (h0 : starts 0 < 3) :
    scanOut2 ((σ.2, ⟨starts 0, h0⟩) : ScanState) (fun i : Fin n => starts i.succ) =
      scanOut2 σ starts := by
  cases n with
  | zero =>
      simp [scanOut2]
  | succ n =>
      cases n <;> simp [scanOut2]

/- Adding a head start shifts the first incoming component on successor indices. -/
private lemma scanPrev2_cons_succ {n : ℕ} (σ σ' : ScanState) (starts : Counts n)
    (hσ' : σ'.1.val = σ.2.val) (k : Fin n) :
    scanPrev2 σ (countsCons σ'.2.val starts) k.succ =
      scanPrev2 σ' starts k := by
  by_cases hk0 : k.val = 0
  · have hk : k = ⟨0, by omega⟩ := Fin.ext hk0
    rw [hk]
    simp [scanPrev2, hσ']
  · by_cases hk1 : k.val = 1
    · have hk : k = ⟨1, by omega⟩ := Fin.ext hk1
      rw [hk]
      simp [scanPrev2, scanStartAt, countsCons]
    · have hle : k.val ≤ n + 1 := by omega
      have hlt : k.val - 2 < n := by omega
      have hne : k.val - 1 ≠ 0 := by omega
      simp [scanPrev2, scanStartAt, countsCons, hk0, hk1, hle, hlt, hne]
      apply congrArg starts
      apply Fin.ext
      simp
      omega

/- Adding a head start shifts the second incoming component on successor indices. -/
private lemma scanPrev1_cons_succ {n : ℕ} (σ σ' : ScanState) (starts : Counts n)
    (k : Fin n) :
    scanPrev1 σ (countsCons σ'.2.val starts) k.succ =
      scanPrev1 σ' starts k := by
  by_cases hk0 : k.val = 0
  · have hk : k = ⟨0, by omega⟩ := Fin.ext hk0
    rw [hk]
    simp [scanPrev1, scanStartAt, countsCons]
  · have hlt : k.val - 1 < n := by omega
    simp [scanPrev1, scanStartAt, countsCons, hk0, hlt]

/- Removing the head shifts the first incoming component on the tail. -/
private lemma scanPrev2_tail {n : ℕ} (σ : ScanState) (starts : Counts (n + 1))
    (h0 : starts 0 < 3) (i : Fin n) :
    scanPrev2 ((σ.2, ⟨starts 0, h0⟩) : ScanState) (fun k : Fin n => starts k.succ) i =
      scanPrev2 σ starts i.succ := by
  by_cases hi0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi]
    simp [scanPrev2]
  · by_cases hi1 : i.val = 1
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
      rw [hi]
      simp [scanPrev2, scanStartAt]
    · have hne : i.val.succ ≠ 1 := by omega
      have hlt2 : i.val - 2 < n := by omega
      have hlt : i.val - 1 < n := by omega
      have hle : i.val ≤ n + 1 := by omega
      simp [scanPrev2, scanStartAt, hi0, hi1, hlt2, hle]
      apply congrArg starts
      apply Fin.ext
      simp
      omega

/- Removing the head shifts the second incoming component on the tail. -/
private lemma scanPrev1_tail {n : ℕ} (σ : ScanState) (starts : Counts (n + 1))
    (h0 : starts 0 < 3) (i : Fin n) :
    scanPrev1 ((σ.2, ⟨starts 0, h0⟩) : ScanState) (fun k : Fin n => starts k.succ) i =
      scanPrev1 σ starts i.succ := by
  by_cases hi0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi]
    simp [scanPrev1, scanStartAt]
  · have hlt : i.val < n + 1 := by omega
    have hltPred : i.val - 1 < n := by omega
    simp [scanPrev1, scanStartAt, hi0, hlt, hltPred]
    apply congrArg starts
    apply Fin.ext
    simp
    omega

/- A coordinate decomposition matching a scan from state `σ` to state `τ`. -/
private def ScanDecomp {n : ℕ} (d : Counts n) (σ τ : ScanState) : Prop :=
  ∃ triplets : Counts n, ∃ starts : Counts n,
    (∀ i : Fin n, starts i < 3) ∧
      τ.1.val = scanOut1 σ starts ∧
      τ.2.val = scanOut2 σ starts ∧
      ∀ i : Fin n,
        d i = scanPrev2 σ starts i + scanPrev1 σ starts i + starts i + 3 * triplets i

/- One scan step follows from the corresponding coordinate equation. -/
private lemma scan_step_of_coord (σ : ScanState) (z s t : ℕ) (hs : s < 3)
    (hz : z = σ.1.val + σ.2.val + s + 3 * t) :
    scanStep σ z = some (σ.2, ⟨s, hs⟩) := by
  have hle : σ.1.val + σ.2.val ≤ z := by omega
  have hmod : (z - σ.1.val - σ.2.val) % 3 = s := by omega
  simp [scanStep, hle, hmod]
  congr

/- A successful scan step yields one triplet count and the next run start. -/
private lemma coord_of_scan_step {σ τ : ScanState} {z : ℕ}
    (h : scanStep σ z = some τ) :
    ∃ t : ℕ,
      z = σ.1.val + σ.2.val + τ.2.val + 3 * t ∧ τ.1 = σ.2 := by
  unfold scanStep at h
  by_cases hle : σ.1.val + σ.2.val ≤ z
  · simp [hle] at h
    subst τ
    refine ⟨(z - σ.1.val - σ.2.val) / 3, ?_, ?_⟩
    · change z = σ.1.val + σ.2.val +
        (z - σ.1.val - σ.2.val) % 3 +
          3 * ((z - σ.1.val - σ.2.val) / 3)
      calc
        z = σ.1.val + σ.2.val + (z - σ.1.val - σ.2.val) := by omega
        _ = σ.1.val + σ.2.val +
            ((z - σ.1.val - σ.2.val) % 3 +
              3 * ((z - σ.1.val - σ.2.val) / 3)) := by
              rw [Nat.mod_add_div]
        _ = σ.1.val + σ.2.val + (z - σ.1.val - σ.2.val) % 3 +
            3 * ((z - σ.1.val - σ.2.val) / 3) := by ring
    · rfl
  · simp [hle] at h

/- Successful scans are equivalent to normalized coordinate decompositions. -/
private lemma scan_iff_scanDecomp {n : ℕ} (d : Counts n) (σ τ : ScanState) :
    scan d σ = some τ ↔ ScanDecomp d σ τ := by
  induction n generalizing σ τ with
  | zero =>
      constructor
      · intro h
        simp [scan] at h
        subst τ
        unfold ScanDecomp
        refine ⟨(fun i : Fin 0 => nomatch i), (fun i : Fin 0 => nomatch i),
          ?_, ?_, ?_, ?_⟩
        · intro i
          exact nomatch i
        · rfl
        · rfl
        · intro i
          exact nomatch i
      · intro h
        rcases h with ⟨triplets, starts, hb, h1, h2, hc⟩
        simp [scan]
        rcases σ with ⟨a, b⟩
        rcases τ with ⟨c, e⟩
        simp [scanOut1, scanOut2] at h1 h2 ⊢
        apply Prod.ext
        · exact Fin.ext h1.symm
        · exact Fin.ext h2.symm
  | succ n ih =>
      constructor
      · intro h
        simp [scan, List.ofFn_succ] at h
        cases hstep : scanStep σ (d 0) with
        | none =>
            simp [hstep] at h
        | some σ' =>
            simp [hstep] at h
            rcases (ih (fun i : Fin n => d i.succ) σ' τ).mp h with
              ⟨tripTail, startTail, hboundTail, hout1, hout2, hcoordTail⟩
            rcases coord_of_scan_step hstep with ⟨t0, hcoord0, hσ'⟩
            have hσ'val : σ'.1.val = σ.2.val := by simp [hσ']
            refine ⟨countsCons t0 tripTail, countsCons σ'.2.val startTail, ?_, ?_, ?_, ?_⟩
            · intro i
              cases i using Fin.cases with
              | zero =>
                  simp [countsCons]
              | succ k =>
                  simpa [countsCons] using hboundTail k
            · rwa [scanOut1_cons σ σ' startTail hσ'val]
            · rwa [scanOut2_cons σ σ' startTail]
            · intro i
              exact Fin.cases
                (by simpa [scanPrev1, scanPrev2, countsCons] using hcoord0)
                (fun k => by
                  rw [scanPrev2_cons_succ σ σ' startTail hσ'val k,
                    scanPrev1_cons_succ σ σ' startTail k]
                  simpa [countsCons] using hcoordTail k)
                i
      · intro h
        rcases h with ⟨triplets, starts, hbound, hout1, hout2, hcoord⟩
        simp [scan, List.ofFn_succ]
        let σ' : ScanState := (σ.2, ⟨starts 0, hbound 0⟩)
        have hstep : scanStep σ (d 0) = some σ' := by
          exact scan_step_of_coord σ (d 0) (starts 0) (triplets 0) (hbound 0) (by
            specialize hcoord 0
            simpa [σ', scanPrev1, scanPrev2] using hcoord)
        rw [hstep]
        apply (ih (fun i : Fin n => d i.succ) σ' τ).mpr
        refine ⟨fun i => triplets i.succ, fun i => starts i.succ, ?_, ?_, ?_, ?_⟩
        · intro i
          exact hbound i.succ
        · dsimp [σ']
          rw [scanOut1_tail σ starts (hbound 0)]
          exact hout1
        · dsimp [σ']
          rw [scanOut2_tail σ starts (hbound 0)]
          exact hout2
        · intro i
          specialize hcoord i.succ
          dsimp [σ']
          rw [scanPrev2_tail σ starts (hbound 0) i,
            scanPrev1_tail σ starts (hbound 0) i]
          simpa using hcoord

/- A run can cover coordinate `i` only when it starts at `i`, `i - 1`, or `i - 2`. -/
private lemma run_cover_at {n : ℕ} (runs : Counts (n - 2)) (i : Fin n) :
    (∑ j : Fin (n - 2),
      if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) =
        scanStartAt runs i.val +
          (if 0 < i.val then scanStartAt runs (i.val - 1) else 0) +
            (if 1 < i.val then scanStartAt runs (i.val - 2) else 0) := by
  calc
    (∑ j : Fin (n - 2),
      if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
        = ∑ j : Fin (n - 2),
            ((if j.val = i.val then runs j else 0) +
              (if 0 < i.val ∧ j.val = i.val - 1 then runs j else 0) +
                (if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hiff :
              (j.val ≤ i.val ∧ i.val ≤ j.val + 2) ↔
                j.val = i.val ∨
                  (0 < i.val ∧ j.val = i.val - 1) ∨
                    (1 < i.val ∧ j.val = i.val - 2) := by
            omega
          by_cases hcover : j.val ≤ i.val ∧ i.val ≤ j.val + 2
          · rcases hiff.mp hcover with h0 | h1 | h2
            · have hnot1' : ¬(0 < i.val ∧ i.val = i.val - 1) := by omega
              have hnot2' : ¬(1 < i.val ∧ i.val = i.val - 2) := by omega
              simp [h0, hnot1', hnot2']
            · have hle : i.val - 1 ≤ i.val := by omega
              have hright : i.val ≤ i.val - 1 + 2 := by omega
              have hnot0' : i.val - 1 ≠ i.val := by omega
              have hnot2' : ¬(1 < i.val ∧ i.val - 1 = i.val - 2) := by omega
              simp [h1, hle, hright, hnot0', hnot2']
            · have hle : i.val - 2 ≤ i.val := by omega
              have hright : i.val ≤ i.val - 2 + 2 := by omega
              have hnot0' : i.val - 2 ≠ i.val := by omega
              have hnot1' : ¬(0 < i.val ∧ i.val - 2 = i.val - 1) := by omega
              simp [h2, hle, hright, hnot0', hnot1']
          · have hnot0 : j.val ≠ i.val := by
              intro h0
              exact hcover ((hiff.mpr (Or.inl h0)))
            have hnot1 : ¬(0 < i.val ∧ j.val = i.val - 1) := by
              intro h1
              exact hcover ((hiff.mpr (Or.inr (Or.inl h1))))
            have hnot2 : ¬(1 < i.val ∧ j.val = i.val - 2) := by
              intro h2
              exact hcover ((hiff.mpr (Or.inr (Or.inr h2))))
            simp [hcover, hnot0, hnot1, hnot2]
    _ = (∑ j : Fin (n - 2), if j.val = i.val then runs j else 0) +
          (∑ j : Fin (n - 2),
            if 0 < i.val ∧ j.val = i.val - 1 then runs j else 0) +
            (∑ j : Fin (n - 2),
              if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = scanStartAt runs i.val +
          (if 0 < i.val then scanStartAt runs (i.val - 1) else 0) +
            (if 1 < i.val then scanStartAt runs (i.val - 2) else 0) := by
          rw [sum_if_fin_val_eq i.val runs]
          change scanStartAt runs i.val +
              (∑ j : Fin (n - 2),
                if 0 < i.val ∧ j.val = i.val - 1 then runs j else 0) +
                (∑ j : Fin (n - 2),
                  if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0) =
            scanStartAt runs i.val +
              (if 0 < i.val then scanStartAt runs (i.val - 1) else 0) +
                (if 1 < i.val then scanStartAt runs (i.val - 2) else 0)
          by_cases hi1 : 0 < i.val
          · have hsum1 :
                (∑ j : Fin (n - 2),
                  if 0 < i.val ∧ j.val = i.val - 1 then runs j else 0) =
                    scanStartAt runs (i.val - 1) := by
                calc
                  (∑ j : Fin (n - 2),
                    if 0 < i.val ∧ j.val = i.val - 1 then runs j else 0)
                      = ∑ j : Fin (n - 2),
                          if j.val = i.val - 1 then runs j else 0 := by
                            apply Finset.sum_congr rfl
                            intro j hj
                            simp [hi1]
                  _ = scanStartAt runs (i.val - 1) := by
                        rw [sum_if_fin_val_eq (i.val - 1) runs]
                        rfl
            rw [if_pos hi1, hsum1]
            by_cases hi2 : 1 < i.val
            · have hsum2 :
                  (∑ j : Fin (n - 2),
                    if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0) =
                      scanStartAt runs (i.val - 2) := by
                  calc
                    (∑ j : Fin (n - 2),
                      if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0)
                        = ∑ j : Fin (n - 2),
                            if j.val = i.val - 2 then runs j else 0 := by
                              apply Finset.sum_congr rfl
                              intro j hj
                              simp [hi2]
                    _ = scanStartAt runs (i.val - 2) := by
                          rw [sum_if_fin_val_eq (i.val - 2) runs]
                          rfl
              rw [if_pos hi2, hsum2]
            · rw [if_neg hi2]
              have hzero :
                  (∑ j : Fin (n - 2),
                    if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0) = 0 := by
                apply Finset.sum_eq_zero
                intro j hj
                simp [hi2]
              rw [hzero]
          · rw [if_neg hi1]
            have hnot2 : ¬1 < i.val := by omega
            have hzero1 :
                (∑ j : Fin (n - 2),
                  if 0 < i.val ∧ j.val = i.val - 1 then runs j else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro j hj
              simp [hi1]
            have hzero2 :
                (∑ j : Fin (n - 2),
                  if 1 < i.val ∧ j.val = i.val - 2 then runs j else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro j hj
              simp [hnot2]
            rw [if_neg hnot2, hzero1, hzero2]

/-- The canonical scan accepts exactly the meldable count vectors. -/
theorem meldable_iff_scanAccepts {n : ℕ} (d : Counts n) :
    Meldable d ↔ ScanAccepts d := by
  constructor
  · intro hd
    rcases hd with ⟨triplets, runs, hcoord⟩
    let starts : Counts n :=
      fun i => if h : i.val < n - 2 then runs ⟨i.val, h⟩ % 3 else 0
    let triplets' : Counts n :=
      fun i =>
        triplets i +
          ∑ j : Fin (n - 2),
            if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j / 3 else 0
    have hdec : ScanDecomp d (0, 0) (0, 0) := by
      refine ⟨triplets', starts, ?hbound, ?hout1, ?hout2, ?hcoord'⟩
      · intro i
        dsimp [starts]
        split_ifs <;> omega
      · dsimp [starts, scanOut1]
        -- The last possible first output component is outside `Fin (n - 2)`,
        -- so the normalized start count there is zero.
        split <;> simp
      · dsimp [starts, scanOut2]
        -- The final start count is also outside `Fin (n - 2)`.
        split <;> simp
      · intro i
        have hi := hcoord i
        -- Remaining bridge: expand the original run cover as normalized
        -- residues plus three times the quotient contribution in `triplets'`,
        -- and identify the three possible covering starts with
        -- `scanPrev2`, `scanPrev1`, and `starts i`.
        have hstartAt : ∀ k : ℕ, scanStartAt starts k = scanStartAt runs k % 3 := by
          intro k
          by_cases hk : k < n - 2
          · have hkn : k < n := by omega
            simp [scanStartAt, starts, hk, hkn]
          · simp [scanStartAt, starts, hk]
        have hquotAt : ∀ k : ℕ,
            scanStartAt (fun j : Fin (n - 2) => runs j / 3) k = scanStartAt runs k / 3 := by
          intro k
          by_cases hk : k < n - 2
          · simp [scanStartAt, hk]
          · simp [scanStartAt, hk]
        have hprev2 : scanPrev2 (0, 0) starts i =
            (if 1 < i.val then scanStartAt runs (i.val - 2) % 3 else 0) := by
          dsimp [scanPrev2]
          by_cases hi0 : i.val = 0
          · simp [hi0]
          · by_cases hi1eq : i.val = 1
            · simp [hi1eq]
            · have hi2 : 1 < i.val := by omega
              simp [hi0, hi1eq, hi2, hstartAt]
        have hprev1 : scanPrev1 (0, 0) starts i =
            (if 0 < i.val then scanStartAt runs (i.val - 1) % 3 else 0) := by
          dsimp [scanPrev1]
          by_cases hi0 : i.val = 0
          · simp [hi0]
          · have hi1 : 0 < i.val := by omega
            simp [hi0, hi1, hstartAt]
        have hstarti : starts i = scanStartAt runs i.val % 3 := by
          dsimp [starts, scanStartAt]
          by_cases hk : i.val < n - 2
          · simp [hk]
          · simp [hk]
        have hcover := run_cover_at runs i
        have hcoverQ := run_cover_at (fun j : Fin (n - 2) => runs j / 3) i
        have hdecomp0 : scanStartAt runs i.val =
            scanStartAt runs i.val % 3 + 3 * (scanStartAt runs i.val / 3) := by
          rw [Nat.mod_add_div]
        have hdecomp1 : (if 0 < i.val then scanStartAt runs (i.val - 1) else 0) =
            (if 0 < i.val then scanStartAt runs (i.val - 1) % 3 else 0) +
              3 * (if 0 < i.val then scanStartAt runs (i.val - 1) / 3 else 0) := by
          by_cases hi1 : 0 < i.val <;> simp [hi1, Nat.mod_add_div]
        have hdecomp2 : (if 1 < i.val then scanStartAt runs (i.val - 2) else 0) =
            (if 1 < i.val then scanStartAt runs (i.val - 2) % 3 else 0) +
              3 * (if 1 < i.val then scanStartAt runs (i.val - 2) / 3 else 0) := by
          by_cases hi2 : 1 < i.val <;> simp [hi2, Nat.mod_add_div]
        rw [hi, hcover]
        dsimp [triplets']
        rw [hcoverQ]
        rw [hprev2, hprev1, hstarti]
        repeat rw [hquotAt]
        omega
    exact (scan_iff_scanDecomp d (0, 0) (0, 0)).mpr hdec
  · intro hscan
    rcases (scan_iff_scanDecomp d (0, 0) (0, 0)).mp hscan with
      ⟨triplets, starts, hbound, hout1, hout2, hcoord⟩
    refine ⟨triplets, (fun j : Fin (n - 2) => starts ⟨j.val, by omega⟩), ?_⟩
    intro i
    have hi := hcoord i
    -- Remaining bridge: the finite sum over `Fin (n - 2)` has exactly the
    -- three possible contributors `i`, `i-1`, and `i-2`; the two output
    -- equalities say the final two normalized starts vanish.
    let runs' : Counts (n - 2) := fun j : Fin (n - 2) => starts ⟨j.val, by omega⟩
    have hout1_zero : ∀ k (hk : k + 2 = n), starts ⟨k, by omega⟩ = 0 := by
      intro k hk
      subst n
      simpa [scanOut1] using hout1.symm
    have hout2_zero : ∀ k (hk : k + 1 = n), starts ⟨k, by omega⟩ = 0 := by
      intro k hk
      subst n
      simpa [scanOut2] using hout2.symm
    have hcurrent : starts i = scanStartAt runs' i.val := by
      by_cases hk : i.val < n - 2
      · dsimp [runs']
        simp [scanStartAt, hk]
      · have hrunzero : scanStartAt runs' i.val = 0 := by
          simp [scanStartAt, hk]
        rw [hrunzero]
        have hcase : i.val + 2 = n ∨ i.val + 1 = n := by omega
        rcases hcase with hN | hN
        · simpa using hout1_zero i.val hN
        · simpa using hout2_zero i.val hN
    have hprev1 : scanPrev1 (0, 0) starts i =
        (if 0 < i.val then scanStartAt runs' (i.val - 1) else 0) := by
      dsimp [scanPrev1]
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hi_pos : 0 < i.val := by omega
        have hlookup : scanStartAt starts (i.val - 1) = scanStartAt runs' (i.val - 1) := by
          by_cases hk : i.val - 1 < n - 2
          · have hkn : i.val - 1 < n := by omega
            dsimp [runs']
            simp [scanStartAt, hk, hkn]
          · have hN : i.val - 1 + 2 = n := by omega
            have hkn : i.val - 1 < n := by omega
            have hleft : scanStartAt starts (i.val - 1) = 0 := by
              simpa [scanStartAt, hkn] using hout1_zero (i.val - 1) hN
            have hright : scanStartAt runs' (i.val - 1) = 0 := by
              simp [scanStartAt, hk]
            rw [hleft, hright]
        simp [hi0, hi_pos, hlookup]
    have hprev2 : scanPrev2 (0, 0) starts i =
        (if 1 < i.val then scanStartAt runs' (i.val - 2) else 0) := by
      dsimp [scanPrev2]
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · by_cases hi1eq : i.val = 1
        · simp [hi1eq]
        · have hi2 : 1 < i.val := by omega
          have hk : i.val - 2 < n - 2 := by omega
          have hkn : i.val - 2 < n := by omega
          dsimp [runs']
          simp [hi0, hi1eq, hi2, scanStartAt, hk, hkn]
    have hcover := run_cover_at runs' i
    rw [hi, hcover]
    rw [hprev2, hprev1, hcurrent]
    omega

/--
On input one, the successful states are exactly `(0,0)`, `(0,1)`, and
`(1,0)`, on which the step follows the displayed three-cycle.
-/
lemma scanStep_one :
    scanStep (0, 0) 1 = some (0, 1) ∧
      scanStep (0, 1) 1 = some (1, 0) ∧
      scanStep (1, 0) 1 = some (0, 0) ∧
      ∀ σ, scanStep σ 1 ≠ none ↔
        σ = (0, 0) ∨ σ = (0, 1) ∨ σ = (1, 0) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · intro σ
    constructor
    · intro h
      rcases σ with ⟨a, b⟩
      fin_cases a <;> fin_cases b <;> simp [scanStep] at h ⊢
    · rintro (rfl | rfl | rfl) <;> simp [scanStep]

/-- Any successful scan of three consecutive singleton counts returns to its start. -/
lemma scan_three_ones (σ τ : ScanState)
    (h : scan (fun _ : Fin 3 ↦ 1) σ = some τ) :
    τ = σ := by
  rcases σ with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [scan, scanStep] at h ⊢
  all_goals subst τ; rfl

end Ninegates
