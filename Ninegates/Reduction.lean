import Ninegates.Scan

namespace Ninegates

/--
Embed an index of the shortened vector into the original vector by skipping
the three coordinates beginning at the zero-based index `j`.
-/
def deleteIndex {n : ℕ} (j : ℕ) (hj : j + 3 ≤ n) :
    Fin (n - 3) → Fin n :=
  fun r ↦
    ⟨if r.val < j then r.val else r.val + 3, by
      split_ifs with hr
      · omega
      · omega⟩

/-- Delete the three coordinates beginning at the zero-based index `j`. -/
def deleteThree {n : ℕ} (c : Counts n) (j : ℕ) (hj : j + 3 ≤ n) :
    Counts (n - 3) :=
  fun r ↦ c (deleteIndex j hj r)

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

/- Cancel a selected `+ 1` when the sum is congruent to two. -/
private lemma modEq_of_add_one_modEq_two {a : ℕ}
    (h : Nat.ModEq 3 (a + 1) 2) :
    Nat.ModEq 3 a 1 := by
  apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1)
  simpa using h

/- Cancel a selected `+ 1` when the sum is congruent to zero. -/
private lemma modEq_of_add_one_modEq_zero {a : ℕ}
    (h : Nat.ModEq 3 (a + 1) 0) :
    Nat.ModEq 3 a 2 := by
  have h' : Nat.ModEq 3 (a + 1) (2 + 1) := by
    exact h.trans (by norm_num)
  exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) h'

/- A term in a zero-valued finite sum of natural numbers is zero. -/
private lemma eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ} (hsum : (∑ i, f i) = 0) (i : ι) :
    f i = 0 := by
  have hle : f i ≤ ∑ j, f j := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/- The unweighted contribution of one run is three tiles. -/
private lemma run_count_sum {n : ℕ} (runs : Fin (n - 2) → ℕ)
    (j : Fin (n - 2)) :
    (∑ i : Fin n,
      if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) =
        3 * runs j := by
  have hj0 : j.val < n := by omega
  have hj1 : j.val + 1 < n := by omega
  have hj2 : j.val + 2 < n := by omega
  calc
    (∑ i : Fin n,
      if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
        = ∑ i : Fin n,
            ((if i.val = j.val then runs j else 0) +
             (if i.val = j.val + 1 then runs j else 0) +
             (if i.val = j.val + 2 then runs j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h0 : i.val = j.val <;>
          by_cases h1 : i.val = j.val + 1 <;>
          by_cases h2 : i.val = j.val + 2 <;>
          simp [h0, h1, h2]; omega
    _ = (∑ i : Fin n, if i.val = j.val then runs j else 0) +
        (∑ i : Fin n, if i.val = j.val + 1 then runs j else 0) +
        (∑ i : Fin n, if i.val = j.val + 2 then runs j else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = runs j + runs j + runs j := by
          rw [sum_if_fin_val_eq j.val (fun _ : Fin n => runs j),
            sum_if_fin_val_eq (j.val + 1) (fun _ : Fin n => runs j),
            sum_if_fin_val_eq (j.val + 2) (fun _ : Fin n => runs j)]
          simp [hj0, hj1, hj2]
    _ = 3 * runs j := by ring

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

/- Total multiplicity strictly left of a cut coordinate. -/
private def leftTotal {n : ℕ} (k : Fin n) (c : Counts n) : ℕ :=
  ∑ i : Fin n, if i.val < k.val then c i else 0

/- Total multiplicity strictly right of a cut coordinate. -/
private def rightTotal {n : ℕ} (k : Fin n) (c : Counts n) : ℕ :=
  ∑ i : Fin n, if k.val < i.val then c i else 0

/- One-based weighted rank sum strictly left of a cut coordinate. -/
private def leftRankSum {n : ℕ} (k : Fin n) (c : Counts n) : ℕ :=
  ∑ i : Fin n, if i.val < k.val then (i.val + 1) * c i else 0

/- One-based weighted rank sum strictly right of a cut coordinate. -/
private def rightRankSum {n : ℕ} (k : Fin n) (c : Counts n) : ℕ :=
  ∑ i : Fin n, if k.val < i.val then (i.val + 1) * c i else 0

/- Filtered totals are additive. -/
private lemma filteredTotal_add {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (a b : Counts n) :
    (∑ i : Fin n, if P i then a i + b i else 0) =
      (∑ i : Fin n, if P i then a i else 0) +
        (∑ i : Fin n, if P i then b i else 0) := by
  calc
    (∑ i : Fin n, if P i then a i + b i else 0)
        = ∑ i : Fin n, ((if P i then a i else 0) + (if P i then b i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hP : P i <;> simp [hP]
    _ = (∑ i : Fin n, if P i then a i else 0) +
          (∑ i : Fin n, if P i then b i else 0) := by
          simp [Finset.sum_add_distrib]

/- Filtered rank sums are additive. -/
private lemma filteredRank_add {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (a b : Counts n) :
    (∑ i : Fin n, if P i then (i.val + 1) * (a i + b i) else 0) =
      (∑ i : Fin n, if P i then (i.val + 1) * a i else 0) +
        (∑ i : Fin n, if P i then (i.val + 1) * b i else 0) := by
  calc
    (∑ i : Fin n, if P i then (i.val + 1) * (a i + b i) else 0)
        = ∑ i : Fin n,
            ((if P i then (i.val + 1) * a i else 0) +
              (if P i then (i.val + 1) * b i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hP : P i <;> simp [hP, Nat.mul_add]
    _ = (∑ i : Fin n, if P i then (i.val + 1) * a i else 0) +
          (∑ i : Fin n, if P i then (i.val + 1) * b i else 0) := by
          simp [Finset.sum_add_distrib]

/- A filtered singleton basis contributes exactly when its index satisfies the filter. -/
private lemma filteredTotal_basis {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (x : Fin n) (m : ℕ) :
    (∑ i : Fin n, if P i then m * basis x i else 0) =
      if P x then m else 0 := by
  by_cases hx : P x
  · calc
      (∑ i : Fin n, if P i then m * basis x i else 0)
          = ∑ i : Fin n, if i = x then m else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hix : i = x
            · subst i
              simp [basis, hx]
            · simp [basis, hix]
      _ = m := by rw [Fintype.sum_ite_eq']
      _ = if P x then m else 0 := by simp [hx]
  · have hzero :
        (∑ i : Fin n, if P i then m * basis x i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hP : P i
      · have hix : i ≠ x := by
          intro h
          subst i
          exact hx hP
        simp [hP, basis, hix]
      · simp [hP]
    rw [hzero]
    simp [hx]

/- A filtered weighted basis contributes its one-based rank when selected. -/
private lemma filteredRank_basis {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (x : Fin n) (m : ℕ) :
    (∑ i : Fin n, if P i then (i.val + 1) * (m * basis x i) else 0) =
      if P x then (x.val + 1) * m else 0 := by
  by_cases hx : P x
  · calc
      (∑ i : Fin n, if P i then (i.val + 1) * (m * basis x i) else 0)
          = ∑ i : Fin n, if i = x then (x.val + 1) * m else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hix : i = x
            · subst i
              simp [basis, hx]
            · simp [basis, hix]
      _ = (x.val + 1) * m := by rw [Fintype.sum_ite_eq']
      _ = if P x then (x.val + 1) * m else 0 := by simp [hx]
  · have hzero :
        (∑ i : Fin n, if P i then (i.val + 1) * (m * basis x i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hP : P i
      · have hix : i ≠ x := by
          intro h
          subst i
          exact hx hP
        simp [hP, basis, hix]
      · simp [hP]
    rw [hzero]
    simp [hx]

/- Adding a basis vector updates a filtered total by one selected tile. -/
private lemma filteredTotal_add_basis {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (c : Counts n) (x : Fin n) :
    (∑ i : Fin n, if P i then c i + basis x i else 0) =
      (∑ i : Fin n, if P i then c i else 0) + if P x then 1 else 0 := by
  rw [filteredTotal_add P c (basis x)]
  have hb := filteredTotal_basis P x 1
  simpa using congrArg (fun t => (∑ i : Fin n, if P i then c i else 0) + t) hb

/- Adding a basis vector updates a filtered rank sum by the selected rank. -/
private lemma filteredRank_add_basis {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (c : Counts n) (x : Fin n) :
    (∑ i : Fin n, if P i then (i.val + 1) * (c i + basis x i) else 0) =
      (∑ i : Fin n, if P i then (i.val + 1) * c i else 0) +
        if P x then x.val + 1 else 0 := by
  rw [filteredRank_add P c (basis x)]
  have hb := filteredRank_basis P x 1
  simpa using congrArg (fun t => (∑ i : Fin n, if P i then (i.val + 1) * c i else 0) + t) hb

/- Removing a pair subtracts two selected tiles from a filtered total. -/
private lemma filteredTotal_removePair_add_pair {n : ℕ}
    (P : Fin n → Prop) [DecidablePred P] (w : Counts n) (p : Fin n)
    (hp : 2 ≤ w p) :
    (∑ i : Fin n, if P i then removePair w p i else 0) +
        (if P p then 2 else 0) =
      (∑ i : Fin n, if P i then w i else 0) := by
  have hpoint : ∀ i : Fin n, removePair w p i + 2 * basis p i = w i := by
    intro i
    by_cases h : i = p
    · subst i
      simp [removePair, basis, Nat.sub_add_cancel hp]
    · simp [removePair, basis, h]
  calc
    (∑ i : Fin n, if P i then removePair w p i else 0) + (if P p then 2 else 0)
        = (∑ i : Fin n, if P i then removePair w p i else 0) +
            (∑ i : Fin n, if P i then 2 * basis p i else 0) := by
            rw [filteredTotal_basis P p 2]
    _ = (∑ i : Fin n, if P i then removePair w p i + 2 * basis p i else 0) := by
          rw [filteredTotal_add]
    _ = (∑ i : Fin n, if P i then w i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hpoint i]

/- Removing a pair subtracts twice the selected one-based rank from a filtered rank sum. -/
private lemma filteredRank_removePair_add_pair {n : ℕ}
    (P : Fin n → Prop) [DecidablePred P] (w : Counts n) (p : Fin n)
    (hp : 2 ≤ w p) :
    (∑ i : Fin n, if P i then (i.val + 1) * removePair w p i else 0) +
        (if P p then (p.val + 1) * 2 else 0) =
      (∑ i : Fin n, if P i then (i.val + 1) * w i else 0) := by
  have hpoint : ∀ i : Fin n, removePair w p i + 2 * basis p i = w i := by
    intro i
    by_cases h : i = p
    · subst i
      simp [removePair, basis, Nat.sub_add_cancel hp]
    · simp [removePair, basis, h]
  calc
    (∑ i : Fin n, if P i then (i.val + 1) * removePair w p i else 0) +
        (if P p then (p.val + 1) * 2 else 0)
        = (∑ i : Fin n, if P i then (i.val + 1) * removePair w p i else 0) +
            (∑ i : Fin n, if P i then (i.val + 1) * (2 * basis p i) else 0) := by
            rw [filteredRank_basis P p 2]
    _ = (∑ i : Fin n,
          if P i then (i.val + 1) * (removePair w p i + 2 * basis p i) else 0) := by
          rw [filteredRank_add]
    _ = (∑ i : Fin n, if P i then (i.val + 1) * w i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hpoint i]

/- Total splits into the parts left of, at, and right of a cut. -/
private lemma total_split_at {n : ℕ} (k : Fin n) (c : Counts n) :
    total c = leftTotal k c + c k + rightTotal k c := by
  unfold total leftTotal rightTotal
  calc
    (∑ i : Fin n, c i)
        = ∑ i : Fin n,
            ((if i.val < k.val then c i else 0) +
              (if i.val = k.val then c i else 0) +
              (if k.val < i.val then c i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hlt : i.val < k.val
          · have hne : i.val ≠ k.val := by omega
            have hnotgt : ¬ k.val < i.val := by omega
            simp [hlt, hne, hnotgt]
          · by_cases heq : i.val = k.val
            · simp [heq]
            · have hgt : k.val < i.val := by omega
              simp [hlt, heq, hgt]
    _ = (∑ i : Fin n, if i.val < k.val then c i else 0) +
          (∑ i : Fin n, if i.val = k.val then c i else 0) +
          (∑ i : Fin n, if k.val < i.val then c i else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = (∑ i : Fin n, if i.val < k.val then c i else 0) +
          c k +
          (∑ i : Fin n, if k.val < i.val then c i else 0) := by
          rw [sum_if_fin_val_eq k.val c]
          simp [k.isLt]

/- Rank sum splits into the parts left of, at, and right of a cut. -/
private lemma rankSum_split_at {n : ℕ} (k : Fin n) (c : Counts n) :
    rankSum c =
      leftRankSum k c + (k.val + 1) * c k + rightRankSum k c := by
  unfold rankSum leftRankSum rightRankSum
  calc
    (∑ i : Fin n, (i.val + 1) * c i)
        = ∑ i : Fin n,
            ((if i.val < k.val then (i.val + 1) * c i else 0) +
              (if i.val = k.val then (i.val + 1) * c i else 0) +
              (if k.val < i.val then (i.val + 1) * c i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hlt : i.val < k.val
          · have hne : i.val ≠ k.val := by omega
            have hnotgt : ¬ k.val < i.val := by omega
            simp [hlt, hne, hnotgt]
          · by_cases heq : i.val = k.val
            · simp [heq]
            · have hgt : k.val < i.val := by omega
              simp [hlt, heq, hgt]
    _ = (∑ i : Fin n, if i.val < k.val then (i.val + 1) * c i else 0) +
          (∑ i : Fin n, if i.val = k.val then (i.val + 1) * c i else 0) +
          (∑ i : Fin n, if k.val < i.val then (i.val + 1) * c i else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = (∑ i : Fin n, if i.val < k.val then (i.val + 1) * c i else 0) +
          (k.val + 1) * c k +
          (∑ i : Fin n, if k.val < i.val then (i.val + 1) * c i else 0) := by
          rw [sum_if_fin_val_eq k.val (fun i : Fin n => (i.val + 1) * c i)]
          simp [k.isLt]

/- Every meldable vector has total divisible by three. -/
private lemma meldable_total_mod {n : ℕ} (d : Counts n) (hd : Meldable d) :
    Nat.ModEq 3 (total d) 0 := by
  rcases hd with ⟨triplets, runs, hd⟩
  unfold total
  have hrewrite :
      (∑ i : Fin n, d i) =
        (∑ i : Fin n, 3 * triplets i) +
          (∑ j : Fin (n - 2), 3 * runs j) := by
    calc
      (∑ i : Fin n, d i)
          = ∑ i : Fin n,
              (3 * triplets i +
                ∑ j : Fin (n - 2),
                  if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hd i]
      _ = (∑ i : Fin n, 3 * triplets i) +
            ∑ i : Fin n,
              (∑ j : Fin (n - 2),
                if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, 3 * triplets i) +
            ∑ j : Fin (n - 2),
              ∑ i : Fin n,
                if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0 := by
              rw [Finset.sum_comm]
      _ = (∑ i : Fin n, 3 * triplets i) +
            ∑ j : Fin (n - 2), 3 * runs j := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              exact run_count_sum runs j
  rw [hrewrite]
  have hTriplets : Nat.ModEq 3 (∑ i : Fin n, 3 * triplets i) 0 := by
    apply sum_modEq_zero
    intro i
    apply Nat.modEq_zero_iff_dvd.mpr
    exact ⟨triplets i, by ring⟩
  have hRuns : Nat.ModEq 3 (∑ j : Fin (n - 2), 3 * runs j) 0 := by
    apply sum_modEq_zero
    intro j
    apply Nat.modEq_zero_iff_dvd.mpr
    exact ⟨runs j, by ring⟩
  simpa using Nat.ModEq.add hTriplets hRuns

/- A run crossing a zero coordinate in a meldable decomposition has count zero. -/
private lemma run_eq_zero_of_zero_coord {n : ℕ} {d : Counts n} {k : Fin n}
    {triplets : Counts n} {runs : Fin (n - 2) → ℕ}
    (hcoord : ∀ i : Fin n,
      d i =
        3 * triplets i +
          ∑ j : Fin (n - 2),
            if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
    (hk0 : d k = 0) {j : Fin (n - 2)}
    (hcover : j.val ≤ k.val ∧ k.val ≤ j.val + 2) :
    runs j = 0 := by
  have hkcoord := hcoord k
  have hsum0 :
      (∑ j : Fin (n - 2),
        if j.val ≤ k.val ∧ k.val ≤ j.val + 2 then runs j else 0) = 0 := by
    omega
  have hterm := eq_zero_of_sum_eq_zero hsum0 j
  simpa [hcover] using hterm

/- One run contributes a multiple of three to the left total across a zero cut. -/
private lemma run_left_count_mod {n : ℕ} (k : Fin n)
    (runs : Fin (n - 2) → ℕ)
    (hzeroCross : ∀ j : Fin (n - 2),
      j.val ≤ k.val ∧ k.val ≤ j.val + 2 → runs j = 0)
    (j : Fin (n - 2)) :
    Nat.ModEq 3
      (∑ i : Fin n,
        if i.val < k.val then
          (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
        else 0)
      0 := by
  by_cases hleft : j.val + 2 < k.val
  · have h_eq :
        (∑ i : Fin n,
          if i.val < k.val then
            (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
          else 0) =
          (∑ i : Fin n,
            if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hcover : j.val ≤ i.val ∧ i.val ≤ j.val + 2
      · have hi_left : i.val < k.val := by omega
        simp [hcover, hi_left]
      · simp [hcover]
    rw [h_eq, run_count_sum]
    apply Nat.modEq_zero_iff_dvd.mpr
    exact ⟨runs j, by ring⟩
  · by_cases hcross : j.val ≤ k.val ∧ k.val ≤ j.val + 2
    · have hruns : runs j = 0 := hzeroCross j hcross
      simp [hruns]
      rfl
    · have hright : k.val < j.val := by omega
      have hzero :
          (∑ i : Fin n,
            if i.val < k.val then
              (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hi_left : i.val < k.val
        · have hnot : ¬ (j.val ≤ i.val ∧ i.val ≤ j.val + 2) := by omega
          simp [hi_left, hnot]
        · simp [hi_left]
      rw [hzero]

/- One run contributes a multiple of three to the left rank sum across a zero cut. -/
private lemma run_left_rank_mod {n : ℕ} (k : Fin n)
    (runs : Fin (n - 2) → ℕ)
    (hzeroCross : ∀ j : Fin (n - 2),
      j.val ≤ k.val ∧ k.val ≤ j.val + 2 → runs j = 0)
    (j : Fin (n - 2)) :
    Nat.ModEq 3
      (∑ i : Fin n,
        if i.val < k.val then
          (i.val + 1) *
            (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
        else 0)
      0 := by
  by_cases hleft : j.val + 2 < k.val
  · have h_eq :
        (∑ i : Fin n,
          if i.val < k.val then
            (i.val + 1) *
              (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
          else 0) =
          (∑ i : Fin n,
            (i.val + 1) *
              (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hcover : j.val ≤ i.val ∧ i.val ≤ j.val + 2
      · have hi_left : i.val < k.val := by omega
        simp [hcover, hi_left]
      · simp [hcover]
    rw [h_eq, run_weight_sum]
    apply Nat.modEq_zero_iff_dvd.mpr
    exact ⟨(j.val + 2) * runs j, by ring⟩
  · by_cases hcross : j.val ≤ k.val ∧ k.val ≤ j.val + 2
    · have hruns : runs j = 0 := hzeroCross j hcross
      simp [hruns]
      rfl
    · have hright : k.val < j.val := by omega
      have hzero :
          (∑ i : Fin n,
            if i.val < k.val then
              (i.val + 1) *
                (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
            else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hi_left : i.val < k.val
        · have hnot : ¬ (j.val ≤ i.val ∧ i.val ≤ j.val + 2) := by omega
          simp [hi_left, hnot]
        · simp [hi_left]
      rw [hzero]

/- The left total of a meldable vector with a zero at the cut is divisible by three. -/
private lemma meldable_leftTotal_mod_of_zero {n : ℕ} (d : Counts n) (k : Fin n)
    (hd : Meldable d) (hk0 : d k = 0) :
    Nat.ModEq 3 (leftTotal k d) 0 := by
  rcases hd with ⟨triplets, runs, hcoord⟩
  have hzeroCross : ∀ j : Fin (n - 2),
      j.val ≤ k.val ∧ k.val ≤ j.val + 2 → runs j = 0 := by
    intro j hcover
    exact run_eq_zero_of_zero_coord hcoord hk0 hcover
  unfold leftTotal
  have hrewrite :
      (∑ i : Fin n, if i.val < k.val then d i else 0) =
        (∑ i : Fin n, if i.val < k.val then 3 * triplets i else 0) +
          (∑ j : Fin (n - 2),
            ∑ i : Fin n,
              if i.val < k.val then
                (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0) := by
    calc
      (∑ i : Fin n, if i.val < k.val then d i else 0)
          = ∑ i : Fin n,
              if i.val < k.val then
                (3 * triplets i +
                  ∑ j : Fin (n - 2),
                    if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hcoord i]
      _ = ∑ i : Fin n,
            ((if i.val < k.val then 3 * triplets i else 0) +
              (if i.val < k.val then
                (∑ j : Fin (n - 2),
                  if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hleft : i.val < k.val <;> simp [hleft]
      _ = (∑ i : Fin n, if i.val < k.val then 3 * triplets i else 0) +
            ∑ i : Fin n,
              if i.val < k.val then
                (∑ j : Fin (n - 2),
                  if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0 := by
              simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, if i.val < k.val then 3 * triplets i else 0) +
            ∑ i : Fin n,
              ∑ j : Fin (n - 2),
                if i.val < k.val then
                  (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
                else 0 := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hleft : i.val < k.val <;> simp [hleft]
      _ = (∑ i : Fin n, if i.val < k.val then 3 * triplets i else 0) +
            ∑ j : Fin (n - 2),
              ∑ i : Fin n,
                if i.val < k.val then
                  (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
                else 0 := by
              rw [Finset.sum_comm]
  rw [hrewrite]
  have hTriplets :
      Nat.ModEq 3 (∑ i : Fin n, if i.val < k.val then 3 * triplets i else 0) 0 := by
    apply sum_modEq_zero
    intro i
    by_cases hleft : i.val < k.val
    · simp [hleft]
      apply Nat.modEq_zero_iff_dvd.mpr
      exact ⟨triplets i, by ring⟩
    · simp [hleft]
      rfl
  have hRuns :
      Nat.ModEq 3
        (∑ j : Fin (n - 2),
          ∑ i : Fin n,
            if i.val < k.val then
              (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
            else 0)
        0 := by
    apply sum_modEq_zero
    intro j
    exact run_left_count_mod k runs hzeroCross j
  simpa using Nat.ModEq.add hTriplets hRuns

/- The left rank sum of a meldable vector with a zero at the cut is divisible by three. -/
private lemma meldable_leftRank_mod_of_zero {n : ℕ} (d : Counts n) (k : Fin n)
    (hd : Meldable d) (hk0 : d k = 0) :
    Nat.ModEq 3 (leftRankSum k d) 0 := by
  rcases hd with ⟨triplets, runs, hcoord⟩
  have hzeroCross : ∀ j : Fin (n - 2),
      j.val ≤ k.val ∧ k.val ≤ j.val + 2 → runs j = 0 := by
    intro j hcover
    exact run_eq_zero_of_zero_coord hcoord hk0 hcover
  unfold leftRankSum
  have hrewrite :
      (∑ i : Fin n, if i.val < k.val then (i.val + 1) * d i else 0) =
        (∑ i : Fin n, if i.val < k.val then (i.val + 1) * (3 * triplets i) else 0) +
          (∑ j : Fin (n - 2),
            ∑ i : Fin n,
              if i.val < k.val then
                (i.val + 1) *
                  (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0) := by
    calc
      (∑ i : Fin n, if i.val < k.val then (i.val + 1) * d i else 0)
          = ∑ i : Fin n,
              if i.val < k.val then
                (i.val + 1) *
                  (3 * triplets i +
                    ∑ j : Fin (n - 2),
                      if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hcoord i]
      _ = ∑ i : Fin n,
            ((if i.val < k.val then (i.val + 1) * (3 * triplets i) else 0) +
              (if i.val < k.val then
                (i.val + 1) *
                  (∑ j : Fin (n - 2),
                    if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hleft : i.val < k.val <;> simp [hleft, Nat.mul_add]
      _ = (∑ i : Fin n, if i.val < k.val then (i.val + 1) * (3 * triplets i) else 0) +
            ∑ i : Fin n,
              if i.val < k.val then
                (i.val + 1) *
                  (∑ j : Fin (n - 2),
                    if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
              else 0 := by
              simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, if i.val < k.val then (i.val + 1) * (3 * triplets i) else 0) +
            ∑ i : Fin n,
              ∑ j : Fin (n - 2),
                if i.val < k.val then
                  (i.val + 1) *
                    (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
                else 0 := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hleft : i.val < k.val <;> simp [hleft, Finset.mul_sum]
      _ = (∑ i : Fin n, if i.val < k.val then (i.val + 1) * (3 * triplets i) else 0) +
            ∑ j : Fin (n - 2),
              ∑ i : Fin n,
                if i.val < k.val then
                  (i.val + 1) *
                    (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
                else 0 := by
              rw [Finset.sum_comm]
  rw [hrewrite]
  have hTriplets :
      Nat.ModEq 3
        (∑ i : Fin n, if i.val < k.val then (i.val + 1) * (3 * triplets i) else 0)
        0 := by
    apply sum_modEq_zero
    intro i
    by_cases hleft : i.val < k.val
    · simp [hleft]
      apply Nat.modEq_zero_iff_dvd.mpr
      exact ⟨(i.val + 1) * triplets i, by ring⟩
    · simp [hleft]
      rfl
  have hRuns :
      Nat.ModEq 3
        (∑ j : Fin (n - 2),
          ∑ i : Fin n,
            if i.val < k.val then
              (i.val + 1) *
                (if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0)
            else 0)
        0 := by
    apply sum_modEq_zero
    intro j
    exact run_left_rank_mod k runs hzeroCross j
  simpa using Nat.ModEq.add hTriplets hRuns

/- The right total of a meldable vector with a zero at the cut is divisible by three. -/
private lemma meldable_rightTotal_mod_of_zero {n : ℕ} (d : Counts n) (k : Fin n)
    (hd : Meldable d) (hk0 : d k = 0) :
    Nat.ModEq 3 (rightTotal k d) 0 := by
  have htotal := meldable_total_mod d hd
  have hleft := meldable_leftTotal_mod_of_zero d k hd hk0
  have hsplit := total_split_at k d
  have hLR0 : Nat.ModEq 3 (leftTotal k d + rightTotal k d) 0 := by
    rw [hsplit, hk0] at htotal
    simpa [add_assoc] using htotal
  have hLRR : Nat.ModEq 3 (leftTotal k d + rightTotal k d) (rightTotal k d) := by
    simpa using Nat.ModEq.add hleft (Nat.ModEq.refl (rightTotal k d))
  exact hLRR.symm.trans hLR0

/- The right rank sum of a meldable vector with a zero at the cut is divisible by three. -/
private lemma meldable_rightRank_mod_of_zero {n : ℕ} (d : Counts n) (k : Fin n)
    (hd : Meldable d) (hk0 : d k = 0) :
    Nat.ModEq 3 (rightRankSum k d) 0 := by
  have hrank := meldable_rankSum_mod d hd
  have hleft := meldable_leftRank_mod_of_zero d k hd hk0
  have hsplit := rankSum_split_at k d
  have hLR0 : Nat.ModEq 3 (leftRankSum k d + rightRankSum k d) 0 := by
    rw [hsplit, hk0] at hrank
    simpa [add_assoc] using hrank
  have hLRR : Nat.ModEq 3 (leftRankSum k d + rightRankSum k d) (rightRankSum k d) := by
    simpa using Nat.ModEq.add hleft (Nat.ModEq.refl (rightRankSum k d))
  exact hLRR.symm.trans hLR0

/-- Every internal coordinate of a live all-rank wait is positive. -/
theorem interior_positive {n : ℕ} (hn : 6 ≤ n) (hdiv : 3 ∣ n)
    {c : Counts n} (hc : LiveWait c) {k : Fin n}
    (hk_left : 1 ≤ k.val) (hk_right : k.val + 1 < n) :
    1 ≤ c k := by
  by_contra hpos
  have hk0 : c k = 0 := by omega
  rcases hc with ⟨hbound, htotal, hcomplete⟩

  have left_draw_residue :
      ∀ x : Fin n, x.val < k.val →
        (Nat.ModEq 3 (leftTotal k c) 1 ∧
            Nat.ModEq 3 (rightTotal k c) 0) ∨
          (Nat.ModEq 3 (leftTotal k c) 2 ∧
            Nat.ModEq 3 (rightTotal k c) 2) := by
    intro x hx
    rcases hcomplete x with ⟨p, hp, hpMeld⟩
    let w : Counts n := fun i => c i + basis x i
    let d : Counts n := removePair w p
    have hx_ne : k ≠ x := by
      intro h
      have : k.val = x.val := by simp [h]
      omega
    have hdk0 : d k = 0 := by
      dsimp [d, w]
      simp [removePair, basis, hk0, hx_ne]
    have hp_ne : p ≠ k := by
      intro hpk
      subst p
      have hwk : w k = 0 := by
        dsimp [w]
        simp [basis, hk0, hx_ne]
      have hpw : 2 ≤ w k := by simpa using hp
      rw [hwk] at hpw
      omega
    have hleftD := meldable_leftTotal_mod_of_zero d k hpMeld hdk0
    have hrightD := meldable_rightTotal_mod_of_zero d k hpMeld hdk0
    have hleftRemove :
        leftTotal k d + (if p.val < k.val then 2 else 0) = leftTotal k w := by
      dsimp [d]
      simpa [leftTotal] using
        filteredTotal_removePair_add_pair (fun i : Fin n => i.val < k.val) w p hp
    have hrightRemove :
        rightTotal k d + (if k.val < p.val then 2 else 0) = rightTotal k w := by
      dsimp [d]
      simpa [rightTotal] using
        filteredTotal_removePair_add_pair (fun i : Fin n => k.val < i.val) w p hp
    have hleftDraw : leftTotal k w = leftTotal k c + 1 := by
      dsimp [w]
      simpa [leftTotal, hx] using
        filteredTotal_add_basis (fun i : Fin n => i.val < k.val) c x
    have hrightDraw : rightTotal k w = rightTotal k c := by
      have hx_not_right : ¬ k.val < x.val := by omega
      dsimp [w]
      simpa [rightTotal, hx_not_right] using
        filteredTotal_add_basis (fun i : Fin n => k.val < i.val) c x
    have hp_side : p.val < k.val ∨ k.val < p.val := by
      have hne : p.val ≠ k.val := by
        intro hv
        exact hp_ne (Fin.ext hv)
      omega
    rcases hp_side with hp_left | hp_right
    · left
      have hleftW2 : Nat.ModEq 3 (leftTotal k w) 2 := by
        rw [← hleftRemove]
        have htmp : Nat.ModEq 3 (leftTotal k d + 2) 2 := by
          simpa using Nat.ModEq.add hleftD (Nat.ModEq.refl 2)
        simpa [hp_left] using htmp
      have hAplus : Nat.ModEq 3 (leftTotal k c + 1) 2 := by
        simpa [hleftDraw] using hleftW2
      have hrightW0 : Nat.ModEq 3 (rightTotal k w) 0 := by
        rw [← hrightRemove]
        have hnot_right : ¬ k.val < p.val := by omega
        simpa [hnot_right] using hrightD
      have hB0 : Nat.ModEq 3 (rightTotal k c) 0 := by
        simpa [hrightDraw] using hrightW0
      exact ⟨modEq_of_add_one_modEq_two hAplus, hB0⟩
    · right
      have hleftW0 : Nat.ModEq 3 (leftTotal k w) 0 := by
        rw [← hleftRemove]
        have hnot_left : ¬ p.val < k.val := by omega
        simpa [hnot_left] using hleftD
      have hAplus : Nat.ModEq 3 (leftTotal k c + 1) 0 := by
        simpa [hleftDraw] using hleftW0
      have hrightW2 : Nat.ModEq 3 (rightTotal k w) 2 := by
        rw [← hrightRemove]
        have htmp : Nat.ModEq 3 (rightTotal k d + 2) 2 := by
          simpa using Nat.ModEq.add hrightD (Nat.ModEq.refl 2)
        simpa [hp_right] using htmp
      have hB2 : Nat.ModEq 3 (rightTotal k c) 2 := by
        simpa [hrightDraw] using hrightW2
      exact ⟨modEq_of_add_one_modEq_zero hAplus, hB2⟩

  have right_draw_residue :
      ∀ x : Fin n, k.val < x.val →
        (Nat.ModEq 3 (leftTotal k c) 2 ∧
            Nat.ModEq 3 (rightTotal k c) 2) ∨
          (Nat.ModEq 3 (leftTotal k c) 0 ∧
            Nat.ModEq 3 (rightTotal k c) 1) := by
    intro x hx
    rcases hcomplete x with ⟨p, hp, hpMeld⟩
    let w : Counts n := fun i => c i + basis x i
    let d : Counts n := removePair w p
    have hx_ne : k ≠ x := by
      intro h
      have : k.val = x.val := by simp [h]
      omega
    have hdk0 : d k = 0 := by
      dsimp [d, w]
      simp [removePair, basis, hk0, hx_ne]
    have hp_ne : p ≠ k := by
      intro hpk
      subst p
      have hwk : w k = 0 := by
        dsimp [w]
        simp [basis, hk0, hx_ne]
      have hpw : 2 ≤ w k := by simpa using hp
      rw [hwk] at hpw
      omega
    have hleftD := meldable_leftTotal_mod_of_zero d k hpMeld hdk0
    have hrightD := meldable_rightTotal_mod_of_zero d k hpMeld hdk0
    have hleftRemove :
        leftTotal k d + (if p.val < k.val then 2 else 0) = leftTotal k w := by
      dsimp [d]
      simpa [leftTotal] using
        filteredTotal_removePair_add_pair (fun i : Fin n => i.val < k.val) w p hp
    have hrightRemove :
        rightTotal k d + (if k.val < p.val then 2 else 0) = rightTotal k w := by
      dsimp [d]
      simpa [rightTotal] using
        filteredTotal_removePair_add_pair (fun i : Fin n => k.val < i.val) w p hp
    have hleftDraw : leftTotal k w = leftTotal k c := by
      have hx_not_left : ¬ x.val < k.val := by omega
      dsimp [w]
      simpa [leftTotal, hx_not_left] using
        filteredTotal_add_basis (fun i : Fin n => i.val < k.val) c x
    have hrightDraw : rightTotal k w = rightTotal k c + 1 := by
      dsimp [w]
      simpa [rightTotal, hx] using
        filteredTotal_add_basis (fun i : Fin n => k.val < i.val) c x
    have hp_side : p.val < k.val ∨ k.val < p.val := by
      have hne : p.val ≠ k.val := by
        intro hv
        exact hp_ne (Fin.ext hv)
      omega
    rcases hp_side with hp_left | hp_right
    · left
      have hleftW2 : Nat.ModEq 3 (leftTotal k w) 2 := by
        rw [← hleftRemove]
        have htmp : Nat.ModEq 3 (leftTotal k d + 2) 2 := by
          simpa using Nat.ModEq.add hleftD (Nat.ModEq.refl 2)
        simpa [hp_left] using htmp
      have hA2 : Nat.ModEq 3 (leftTotal k c) 2 := by
        simpa [hleftDraw] using hleftW2
      have hrightW0 : Nat.ModEq 3 (rightTotal k w) 0 := by
        rw [← hrightRemove]
        have hnot_right : ¬ k.val < p.val := by omega
        simpa [hnot_right] using hrightD
      have hBplus : Nat.ModEq 3 (rightTotal k c + 1) 0 := by
        simpa [hrightDraw] using hrightW0
      exact ⟨hA2, modEq_of_add_one_modEq_zero hBplus⟩
    · right
      have hleftW0 : Nat.ModEq 3 (leftTotal k w) 0 := by
        rw [← hleftRemove]
        have hnot_left : ¬ p.val < k.val := by omega
        simpa [hnot_left] using hleftD
      have hA0 : Nat.ModEq 3 (leftTotal k c) 0 := by
        simpa [hleftDraw] using hleftW0
      have hrightW2 : Nat.ModEq 3 (rightTotal k w) 2 := by
        rw [← hrightRemove]
        have htmp : Nat.ModEq 3 (rightTotal k d + 2) 2 := by
          simpa using Nat.ModEq.add hrightD (Nat.ModEq.refl 2)
        simpa [hp_right] using htmp
      have hBplus : Nat.ModEq 3 (rightTotal k c + 1) 2 := by
        simpa [hrightDraw] using hrightW2
      exact ⟨hA0, modEq_of_add_one_modEq_two hBplus⟩

  let xLeft : Fin n := ⟨0, by omega⟩
  have hxLeft : xLeft.val < k.val := by
    dsimp [xLeft]
    omega
  let xRight : Fin n := ⟨k.val + 1, hk_right⟩
  have hxRight : k.val < xRight.val := by
    dsimp [xRight]
    omega
  have hLeftResidue := left_draw_residue xLeft hxLeft
  have hRightResidue := right_draw_residue xRight hxRight
  have hAB :
      Nat.ModEq 3 (leftTotal k c) 2 ∧
        Nat.ModEq 3 (rightTotal k c) 2 := by
    rcases hLeftResidue with hL | hL
    · rcases hRightResidue with hR | hR
      · exact hR
      · exfalso
        have hbad : Nat.ModEq 3 1 0 := hL.1.symm.trans hR.1
        norm_num at hbad
    · exact hL

  have left_draw_rank_mod :
      ∀ x : Fin n, x.val < k.val →
        Nat.ModEq 3 (leftRankSum k c + (x.val + 1)) 0 := by
    intro x hx
    rcases hcomplete x with ⟨p, hp, hpMeld⟩
    let w : Counts n := fun i => c i + basis x i
    let d : Counts n := removePair w p
    have hx_ne : k ≠ x := by
      intro h
      have : k.val = x.val := by simp [h]
      omega
    have hdk0 : d k = 0 := by
      dsimp [d, w]
      simp [removePair, basis, hk0, hx_ne]
    have hp_ne : p ≠ k := by
      intro hpk
      subst p
      have hwk : w k = 0 := by
        dsimp [w]
        simp [basis, hk0, hx_ne]
      have hpw : 2 ≤ w k := by simpa using hp
      rw [hwk] at hpw
      omega
    have hleftD := meldable_leftTotal_mod_of_zero d k hpMeld hdk0
    have hleftRankD := meldable_leftRank_mod_of_zero d k hpMeld hdk0
    have hleftRemove :
        leftTotal k d + (if p.val < k.val then 2 else 0) = leftTotal k w := by
      dsimp [d]
      simpa [leftTotal] using
        filteredTotal_removePair_add_pair (fun i : Fin n => i.val < k.val) w p hp
    have hleftDraw : leftTotal k w = leftTotal k c + 1 := by
      dsimp [w]
      simpa [leftTotal, hx] using
        filteredTotal_add_basis (fun i : Fin n => i.val < k.val) c x
    have hp_not_left : ¬ p.val < k.val := by
      intro hp_left
      have hleftW2 : Nat.ModEq 3 (leftTotal k w) 2 := by
        rw [← hleftRemove]
        have htmp : Nat.ModEq 3 (leftTotal k d + 2) 2 := by
          simpa using Nat.ModEq.add hleftD (Nat.ModEq.refl 2)
        simpa [hp_left] using htmp
      have hAplus : Nat.ModEq 3 (leftTotal k c + 1) 2 := by
        simpa [hleftDraw] using hleftW2
      have hA1 := modEq_of_add_one_modEq_two hAplus
      have hbad : Nat.ModEq 3 1 2 := hA1.symm.trans hAB.1
      norm_num at hbad
    have hleftRankRemove :
        leftRankSum k d +
            (if p.val < k.val then (p.val + 1) * 2 else 0) =
          leftRankSum k w := by
      dsimp [d]
      simpa [leftRankSum] using
        filteredRank_removePair_add_pair (fun i : Fin n => i.val < k.val) w p hp
    have hleftRankDraw :
        leftRankSum k w = leftRankSum k c + (x.val + 1) := by
      dsimp [w]
      simpa [leftRankSum, hx] using
        filteredRank_add_basis (fun i : Fin n => i.val < k.val) c x
    have hleftW0 : Nat.ModEq 3 (leftRankSum k w) 0 := by
      rw [← hleftRankRemove]
      simpa [hp_not_left] using hleftRankD
    simpa [hleftRankDraw] using hleftW0

  have right_draw_rank_mod :
      ∀ x : Fin n, k.val < x.val →
        Nat.ModEq 3 (rightRankSum k c + (x.val + 1)) 0 := by
    intro x hx
    rcases hcomplete x with ⟨p, hp, hpMeld⟩
    let w : Counts n := fun i => c i + basis x i
    let d : Counts n := removePair w p
    have hx_ne : k ≠ x := by
      intro h
      have : k.val = x.val := by simp [h]
      omega
    have hdk0 : d k = 0 := by
      dsimp [d, w]
      simp [removePair, basis, hk0, hx_ne]
    have hp_ne : p ≠ k := by
      intro hpk
      subst p
      have hwk : w k = 0 := by
        dsimp [w]
        simp [basis, hk0, hx_ne]
      have hpw : 2 ≤ w k := by simpa using hp
      rw [hwk] at hpw
      omega
    have hrightD := meldable_rightTotal_mod_of_zero d k hpMeld hdk0
    have hrightRankD := meldable_rightRank_mod_of_zero d k hpMeld hdk0
    have hrightRemove :
        rightTotal k d + (if k.val < p.val then 2 else 0) = rightTotal k w := by
      dsimp [d]
      simpa [rightTotal] using
        filteredTotal_removePair_add_pair (fun i : Fin n => k.val < i.val) w p hp
    have hrightDraw : rightTotal k w = rightTotal k c + 1 := by
      dsimp [w]
      simpa [rightTotal, hx] using
        filteredTotal_add_basis (fun i : Fin n => k.val < i.val) c x
    have hp_not_right : ¬ k.val < p.val := by
      intro hp_right
      have hrightW2 : Nat.ModEq 3 (rightTotal k w) 2 := by
        rw [← hrightRemove]
        have htmp : Nat.ModEq 3 (rightTotal k d + 2) 2 := by
          simpa using Nat.ModEq.add hrightD (Nat.ModEq.refl 2)
        simpa [hp_right] using htmp
      have hBplus : Nat.ModEq 3 (rightTotal k c + 1) 2 := by
        simpa [hrightDraw] using hrightW2
      have hB1 := modEq_of_add_one_modEq_two hBplus
      have hbad : Nat.ModEq 3 1 2 := hB1.symm.trans hAB.2
      norm_num at hbad
    have hrightRankRemove :
        rightRankSum k d +
            (if k.val < p.val then (p.val + 1) * 2 else 0) =
          rightRankSum k w := by
      dsimp [d]
      simpa [rightRankSum] using
        filteredRank_removePair_add_pair (fun i : Fin n => k.val < i.val) w p hp
    have hrightRankDraw :
        rightRankSum k w = rightRankSum k c + (x.val + 1) := by
      dsimp [w]
      simpa [rightRankSum, hx] using
        filteredRank_add_basis (fun i : Fin n => k.val < i.val) c x
    have hrightW0 : Nat.ModEq 3 (rightRankSum k w) 0 := by
      rw [← hrightRankRemove]
      simpa [hp_not_right] using hrightRankD
    simpa [hrightRankDraw] using hrightW0

  have hk_le_one : k.val ≤ 1 := by
    by_contra hknot
    have hk_two : 2 ≤ k.val := by omega
    let y0 : Fin n := ⟨0, by omega⟩
    let y1 : Fin n := ⟨1, by omega⟩
    have hy0 : y0.val < k.val := by
      dsimp [y0]
      omega
    have hy1 : y1.val < k.val := by
      dsimp [y1]
      omega
    have h0 : Nat.ModEq 3 (leftRankSum k c + 1) 0 := by
      simpa [y0] using left_draw_rank_mod y0 hy0
    have h1 : Nat.ModEq 3 (leftRankSum k c + 2) 0 := by
      simpa [y1] using left_draw_rank_mod y1 hy1
    have hsame : Nat.ModEq 3 (leftRankSum k c + 1) (leftRankSum k c + 2) :=
      h0.trans h1.symm
    have hbad : Nat.ModEq 3 1 2 :=
      Nat.ModEq.add_left_cancel (Nat.ModEq.refl (leftRankSum k c)) hsame
    norm_num at hbad

  have hn_le_k_two : n ≤ k.val + 2 := by
    by_contra hnnot
    have hk_two_right : k.val + 2 < n := by omega
    let z0 : Fin n := ⟨k.val + 1, by omega⟩
    let z1 : Fin n := ⟨k.val + 2, hk_two_right⟩
    have hz0 : k.val < z0.val := by
      dsimp [z0]
      omega
    have hz1 : k.val < z1.val := by
      dsimp [z1]
      omega
    have h0 : Nat.ModEq 3 (rightRankSum k c + (k.val + 2)) 0 := by
      simpa [z0, add_assoc] using right_draw_rank_mod z0 hz0
    have h1 : Nat.ModEq 3 (rightRankSum k c + (k.val + 3)) 0 := by
      simpa [z1, add_assoc] using right_draw_rank_mod z1 hz1
    have hsame :
        Nat.ModEq 3
          (rightRankSum k c + (k.val + 2))
          (rightRankSum k c + (k.val + 3)) :=
      h0.trans h1.symm
    have hdiff : Nat.ModEq 3 (k.val + 2) (k.val + 3) :=
      Nat.ModEq.add_left_cancel (Nat.ModEq.refl (rightRankSum k c)) hsame
    have hbad : Nat.ModEq 3 2 3 :=
      Nat.ModEq.add_left_cancel (Nat.ModEq.refl k.val) hdiff
    norm_num at hbad

  omega

/- Folding over an appended list in the `Option` monad. -/
private lemma foldlM_append_option {α σ : Type*} (f : σ → α → Option σ)
    (l₁ l₂ : List α) (s : σ) :
    (l₁ ++ l₂).foldlM f s =
      (l₁.foldlM f s >>= fun s' => l₂.foldlM f s') := by
  induction l₁ generalizing s with
  | nil =>
      simp
  | cons a as ih =>
      simp [List.foldlM]
      cases f s a <;> simp

/- A successful scan is unchanged by deleting a successful block `[1,1,1]`. -/
private lemma scan_delete_three_ones_block
    (pref suff : List ℕ) (σ τ : ScanState)
    (h : (pref ++ [1, 1, 1] ++ suff).foldlM scanStep σ = some τ) :
    (pref ++ suff).foldlM scanStep σ = some τ := by
  rw [foldlM_append_option] at h ⊢
  cases hp : pref.foldlM scanStep σ with
  | none =>
      simp [hp] at h
  | some σp =>
      simp [hp] at h ⊢
      cases h1 : scanStep σp 1 with
      | none =>
          simp [h1] at h
      | some σ1 =>
          cases h2 : scanStep σ1 1 with
          | none =>
              simp [h1, h2] at h
          | some σ2 =>
              cases h3 : scanStep σ2 1 with
              | none =>
                  simp [h1, h2, h3] at h
              | some σ3 =>
                  simp [h1, h2, h3] at h
                  have hscan : scan (fun _ : Fin 3 => 1) σp = some σ3 := by
                    simp [scan, List.ofFn_succ, h1, h2, h3]
                  have hsame : σ3 = σp := scan_three_ones σp σ3 hscan
                  subst σ3
                  exact h

/- The list underlying `deleteThree` is the original list with that slice removed. -/
private lemma ofFn_deleteThree_eq_take_drop {n : ℕ} (d : Counts n) (j : ℕ)
    (hj : j + 3 ≤ n) :
    List.ofFn (fun r => deleteThree d j hj r) =
      (List.ofFn d).take j ++ (List.ofFn d).drop (j + 3) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_ofFn, List.getElem?_append, List.getElem?_take,
    List.getElem?_drop, List.length_take, List.length_ofFn]
  by_cases hi : i < n - 3
  · simp [hi]
    by_cases hij : i < j
    · have hin : i < n := by omega
      simp [hij, hin, deleteThree, deleteIndex]
    · have hidx : j + 3 + (i - min j n) = i + 3 := by omega
      have hi3 : i + 3 < n := by omega
      simp [hi3, hidx, deleteThree, deleteIndex, hij]
  · simp [hi]
    by_cases ht : i < min j n
    · have : i < n - 3 := by omega
      contradiction
    · have hidxge : ¬ j + 3 + (i - min j n) < n := by omega
      simp [hidxge]
      omega

/- Singleton coordinates split the original scan list into prefix, block, suffix. -/
private lemma ofFn_eq_take_ones_drop {n : ℕ} (d : Counts n) (j : ℕ)
    (hj : j + 3 ≤ n)
    (hsingle : ∀ r : Fin n, j ≤ r.val → r.val < j + 3 → d r = 1) :
    List.ofFn d =
      (List.ofFn d).take j ++ [1, 1, 1] ++ (List.ofFn d).drop (j + 3) := by
  let l := List.ofFn d
  have hlen : l.length = n := by simp [l]
  have hj0 : j < l.length := by omega
  have hj1 : j + 1 < l.length := by omega
  have hj2 : j + 2 < l.length := by omega
  have h0 : l[j] = 1 := by
    dsimp [l]
    rw [List.getElem_ofFn]
    convert hsingle (⟨j, by omega⟩ : Fin n) (by simp)
      (by change j < j + 3; omega) using 1
  have h1 : l[j + 1] = 1 := by
    dsimp [l]
    rw [List.getElem_ofFn]
    convert hsingle (⟨j + 1, by omega⟩ : Fin n) (by simp)
      (by change j + 1 < j + 3; omega) using 1
  have h2 : l[j + 2] = 1 := by
    dsimp [l]
    rw [List.getElem_ofFn]
    convert hsingle (⟨j + 2, by omega⟩ : Fin n) (by simp)
      (by change j + 2 < j + 3; omega) using 1
  calc
    List.ofFn d = l := rfl
    _ = l.take j ++ l.drop j := (List.take_append_drop j l).symm
    _ = l.take j ++ (l[j] :: l.drop (j + 1)) := by
      rw [List.drop_eq_getElem_cons hj0]
    _ = l.take j ++ (1 :: l.drop (j + 1)) := by
      rw [h0]
    _ = l.take j ++ (1 :: l[j + 1] :: l.drop (j + 2)) := by
      rw [List.drop_eq_getElem_cons hj1]
    _ = l.take j ++ (1 :: 1 :: l.drop (j + 2)) := by
      rw [h1]
    _ = l.take j ++ (1 :: 1 :: l[j + 2] :: l.drop (j + 3)) := by
      rw [List.drop_eq_getElem_cons hj2]
    _ = l.take j ++ (1 :: 1 :: 1 :: l.drop (j + 3)) := by
      rw [h2]
    _ = (List.ofFn d).take j ++ [1, 1, 1] ++ (List.ofFn d).drop (j + 3) := by
      simp [l]

/- The finite total agrees with summing the list underlying the count vector. -/
private lemma total_eq_list_sum {n : ℕ} (c : Counts n) :
    total c = (List.ofFn c).sum := by
  induction n with
  | zero =>
      simp [total]
  | succ n ih =>
      rw [total, Fin.sum_univ_succ]
      have htail := ih (fun i : Fin n => c i.succ)
      simp [List.ofFn_succ, total] at htail ⊢
      exact htail

/- The embedding of retained indices is injective. -/
private lemma deleteIndex_injective {n : ℕ} (j : ℕ) (hj : j + 3 ≤ n) :
    Function.Injective (deleteIndex j hj) := by
  intro a b h
  apply Fin.ext
  simp [deleteIndex] at h
  by_cases ha : a.val < j <;>
    by_cases hb : b.val < j <;>
      simp [ha, hb] at h <;> omega

/- A retained embedded index never lands in the deleted block. -/
private lemma deleteIndex_not_deleted {n : ℕ} (j : ℕ) (hj : j + 3 ≤ n)
    (r : Fin (n - 3)) :
    ¬ (j ≤ (deleteIndex j hj r).val ∧ (deleteIndex j hj r).val < j + 3) := by
  unfold deleteIndex
  by_cases hr : r.val < j
  · simp [hr]
  · simp [hr]

/- Every index outside the deleted block is in the image of `deleteIndex`. -/
private lemma deleteIndex_preimage_of_not_deleted {n : ℕ} (j : ℕ)
    (hj : j + 3 ≤ n) (p : Fin n)
    (hnot : ¬ (j ≤ p.val ∧ p.val < j + 3)) :
    ∃ p' : Fin (n - 3), deleteIndex j hj p' = p := by
  by_cases hpb : p.val < j
  · refine ⟨⟨p.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [deleteIndex, hpb]
  · have hge : j + 3 ≤ p.val := by
      by_contra hlt
      exact hnot ⟨by omega, by omega⟩
    refine ⟨⟨p.val - 3, by omega⟩, ?_⟩
    apply Fin.ext
    have hnotlt : ¬ p.val - 3 < j := by omega
    simp [deleteIndex, hnotlt]
    omega

/- Basis vectors commute with the retained-index embedding. -/
private lemma basis_deleteIndex {n : ℕ} (j : ℕ) (hj : j + 3 ≤ n)
    (x r : Fin (n - 3)) :
    basis (deleteIndex j hj x) (deleteIndex j hj r) = basis x r := by
  by_cases h : r = x
  · subst r
    simp [basis]
  · have hne : deleteIndex j hj r ≠ deleteIndex j hj x := by
      intro heq
      exact h (deleteIndex_injective j hj heq)
    simp [basis, h, hne]

/- Deletion is compatible with drawing a retained tile and removing a retained pair. -/
private lemma deleteThree_removePair_add_basis {n : ℕ} (c : Counts n)
    (j : ℕ) (hj : j + 3 ≤ n) (x' p' : Fin (n - 3)) :
    deleteThree
        (removePair (fun i : Fin n => c i + basis (deleteIndex j hj x') i)
          (deleteIndex j hj p')) j hj =
      removePair (fun i : Fin (n - 3) => deleteThree c j hj i + basis x' i) p' := by
  funext r
  simp [deleteThree, removePair, basis_deleteIndex]

/--
Deleting three consecutive singleton coordinates from a meldable vector
preserves meldability.
-/
lemma delete_three_meldable {n : ℕ} (d : Counts n) (j : ℕ)
    (hj : j + 3 ≤ n) (hd : Meldable d)
    (hsingle : ∀ r : Fin n, j ≤ r.val → r.val < j + 3 → d r = 1) :
    Meldable (deleteThree d j hj) := by
  apply (meldable_iff_scanAccepts (deleteThree d j hj)).mpr
  have hscan : scan d ((0, 0) : ScanState) = some ((0, 0) : ScanState) :=
    (meldable_iff_scanAccepts d).mp hd
  have hdel := ofFn_deleteThree_eq_take_drop d j hj
  have hfull := ofFn_eq_take_ones_drop d j hj hsingle
  dsimp [ScanAccepts]
  change (List.ofFn (fun r => deleteThree d j hj r)).foldlM scanStep
      ((0, 0) : ScanState) = some ((0, 0) : ScanState)
  rw [hdel]
  apply scan_delete_three_ones_block ((List.ofFn d).take j)
    ((List.ofFn d).drop (j + 3)) ((0, 0) : ScanState) ((0, 0) : ScanState)
  rw [← hfull]
  change scan d ((0, 0) : ScanState) = some ((0, 0) : ScanState)
  exact hscan

/--
Deleting three internal singleton coordinates preserves a live all-rank
wait.
-/
theorem delete_three_live_wait {n : ℕ} (hn : 9 ≤ n) (hdiv : 3 ∣ n)
    (c : Counts n) (hc : LiveWait c) (j : ℕ)
    (hj_left : 1 ≤ j) (hj_right : j + 3 < n)
    (hsingle : ∀ r : Fin n, j ≤ r.val → r.val < j + 3 → c r = 1) :
    LiveWait (deleteThree c j (Nat.le_of_lt hj_right)) := by
  let hj : j + 3 ≤ n := Nat.le_of_lt hj_right
  have _hleft : 1 ≤ j := hj_left
  change LiveWait (deleteThree c j hj)
  rcases hc with ⟨hbound, htotal, hcomplete⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact hbound (deleteIndex j hj r)
  · have hdelSum :
        total (deleteThree c j hj) =
          ((List.ofFn c).take j).sum + ((List.ofFn c).drop (j + 3)).sum := by
      rw [total_eq_list_sum (deleteThree c j hj)]
      change (List.ofFn (fun r => deleteThree c j hj r)).sum =
        ((List.ofFn c).take j).sum + ((List.ofFn c).drop (j + 3)).sum
      rw [ofFn_deleteThree_eq_take_drop c j hj]
      simp [List.sum_append]
    have hfullSum :
        (List.ofFn c).sum =
          ((List.ofFn c).take j).sum + 3 + ((List.ofFn c).drop (j + 3)).sum := by
      have hfull := congrArg List.sum (ofFn_eq_take_ones_drop c j hj hsingle)
      simp [List.sum_append] at hfull
      omega
    have hcSum : (List.ofFn c).sum = n + 4 := by
      rw [← total_eq_list_sum c]
      exact htotal
    rw [hdelSum]
    omega
  · intro x'
    let x : Fin n := deleteIndex j hj x'
    rcases hcomplete x with ⟨p, hp, hpMeld⟩
    have hx_not_deleted :
        ¬ (j ≤ x.val ∧ x.val < j + 3) := by
      dsimp [x]
      exact deleteIndex_not_deleted j hj x'
    have hp_not_deleted :
        ¬ (j ≤ p.val ∧ p.val < j + 3) := by
      intro hpdel
      have hx_ne : p ≠ x := by
        intro hpx
        subst p
        exact hx_not_deleted hpdel
      have hpone : (fun i : Fin n => c i + basis x i) p = 1 := by
        have hcp : c p = 1 := hsingle p hpdel.1 hpdel.2
        simp [basis, hx_ne, hcp]
      rw [hpone] at hp
      omega
    rcases deleteIndex_preimage_of_not_deleted j hj p hp_not_deleted with
      ⟨p', hpidx⟩
    refine ⟨p', ?_, ?_⟩
    · have hp_at_idx :
          2 ≤ c (deleteIndex j hj p') + basis x (deleteIndex j hj p') := by
        simpa [hpidx] using hp
      simpa [deleteThree, x, basis_deleteIndex] using hp_at_idx
    · have hpMeldIdx :
          Meldable
            (removePair
              (fun i : Fin n => c i + basis (deleteIndex j hj x') i)
              (deleteIndex j hj p')) := by
        simpa [x, hpidx] using hpMeld
      have hsingleDorig :
          ∀ r : Fin n, j ≤ r.val → r.val < j + 3 →
            removePair (fun i : Fin n => c i + basis x i) p r = 1 := by
        intro r hrL hrR
        have hx_ne : r ≠ x := by
          intro hrx
          subst r
          exact hx_not_deleted ⟨hrL, hrR⟩
        have hp_ne : r ≠ p := by
          intro hrp
          subst r
          exact hp_not_deleted ⟨hrL, hrR⟩
        simp [removePair, basis, hx_ne, hp_ne, hsingle r hrL hrR]
      have hsingleD :
          ∀ r : Fin n, j ≤ r.val → r.val < j + 3 →
            removePair
              (fun i : Fin n => c i + basis (deleteIndex j hj x') i)
              (deleteIndex j hj p') r = 1 := by
        simpa [x, hpidx] using hsingleDorig
      have hdelMeld :
          Meldable
            (deleteThree
              (removePair
                (fun i : Fin n => c i + basis (deleteIndex j hj x') i)
                (deleteIndex j hj p')) j hj) :=
        delete_three_meldable
          (removePair
            (fun i : Fin n => c i + basis (deleteIndex j hj x') i)
            (deleteIndex j hj p')) j hj hpMeldIdx hsingleD
      rw [deleteThree_removePair_add_basis c j hj x' p'] at hdelMeld
      exact hdelMeld

/--
Deleting three internal singleton coordinates preserves and reflects the
standard hand.
-/
theorem delete_three_standard_iff {n : ℕ} (c : Counts n) (j : ℕ)
    (hj_left : 1 ≤ j) (hj_right : j + 3 < n)
    (hsingle : ∀ r : Fin n, j ≤ r.val → r.val < j + 3 → c r = 1) :
    c = standard n ↔
      deleteThree c j (Nat.le_of_lt hj_right) = standard (n - 3) := by
  constructor
  · intro hc
    subst c
    funext r
    simp only [deleteThree, deleteIndex, standard]
    by_cases hr : r.val < j
    · simp [hr]
      split_ifs <;> omega
    · simp [hr]
      split_ifs <;> omega
  · intro hc
    funext i
    by_cases hbefore : i.val < j
    · let r : Fin (n - 3) := ⟨i.val, by omega⟩
      have hidx : deleteIndex j (Nat.le_of_lt hj_right) r = i := by
        apply Fin.ext
        simp [deleteIndex, r, hbefore]
      have hr := congrFun hc r
      rw [deleteThree, hidx] at hr
      calc
        c i = standard (n - 3) r := hr
        _ = standard n i := by
          simp [standard, r]
          split_ifs <;> omega
    · by_cases hdeleted : i.val < j + 3
      · have hci : c i = 1 := hsingle i (by omega) hdeleted
        rw [hci]
        simp only [standard]
        split_ifs <;> omega
      · let r : Fin (n - 3) := ⟨i.val - 3, by omega⟩
        have hr_ge : j ≤ r.val := by
          simp [r]
          omega
        have hidx : deleteIndex j (Nat.le_of_lt hj_right) r = i := by
          apply Fin.ext
          simp [deleteIndex, r, not_lt_of_ge hr_ge]
          omega
        have hr := congrFun hc r
        rw [deleteThree, hidx] at hr
        calc
          c i = standard (n - 3) r := hr
          _ = standard n i := by
            simp [standard, r]
            split_ifs <;> omega

end Ninegates
