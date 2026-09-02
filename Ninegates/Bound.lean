import Ninegates.Reduction

namespace Ninegates

/-- A live all-rank wait of size `n` that is not the standard hand. -/
def CounterexampleAt (n : ℕ) : Prop :=
  ∃ c : Counts n, LiveWait c ∧ c ≠ standard n

/-- The finite set of sizes to which any counterexample can be reduced. -/
def smallSizes : Finset ℕ :=
  {6, 9, 12, 15, 18, 21}

/- Internal coordinates, represented as the image of `Fin (n - 2)` under
the shift `r ↦ r + 1`. This gives a convenient cardinality proof. -/
private def internalEmbedding (n : ℕ) : Fin (n - 2) ↪ Fin n where
  toFun r := ⟨r.val + 1, by omega⟩
  inj' := by
    intro r s hrs
    apply Fin.ext
    have := congrArg Fin.val hrs
    simp at this
    omega

private def internalIndices (n : ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin (n - 2))).map (internalEmbedding n)

private lemma mem_internalIndices {n : ℕ} {i : Fin n} :
    i ∈ internalIndices n ↔ 1 ≤ i.val ∧ i.val + 1 < n := by
  constructor
  · intro hi
    simp only [internalIndices, Finset.mem_map, Finset.mem_univ, true_and] at hi
    rcases hi with ⟨r, hri⟩
    rw [← hri]
    simp [internalEmbedding]
    omega
  · intro hi
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [internalEmbedding]
    omega

private lemma card_internalIndices (n : ℕ) :
    (internalIndices n).card = n - 2 := by
  simp [internalIndices]

private lemma smallSizes_mem_of_admissible_le_22 {n : ℕ}
    (hn6 : 6 ≤ n) (hdiv : 3 ∣ n) (hn22 : n ≤ 22) :
    n ∈ smallSizes := by
  rcases hdiv with ⟨k, rfl⟩
  have hk2 : 2 ≤ k := by omega
  have hk7 : k ≤ 7 := by omega
  interval_cases k <;> simp [smallSizes]

private lemma internal_excess_le_six {n : ℕ} {c : Counts n}
    (hn6 : 6 ≤ n) (hdiv : 3 ∣ n) (hc : LiveWait c) :
    (internalIndices n).sum (fun i => c i - 1) ≤ 6 := by
  have htotal : total c = n + 4 := hc.2.1
  have hpos :
      ∀ i ∈ internalIndices n, 1 ≤ c i := by
    intro i hi
    have hi' := (mem_internalIndices.mp hi)
    exact interior_positive hn6 hdiv hc hi'.1 hi'.2
  have hadd :
      (internalIndices n).sum (fun i => c i - 1) + (internalIndices n).card =
        (internalIndices n).sum fun i => c i := by
    calc
      (internalIndices n).sum (fun i => c i - 1) + (internalIndices n).card
          = (internalIndices n).sum (fun i => c i - 1) +
              (internalIndices n).sum (fun _ => 1) := by
                rw [Finset.card_eq_sum_ones]
      _ = (internalIndices n).sum (fun i => (c i - 1) + 1) := by
                rw [← Finset.sum_add_distrib]
      _ = (internalIndices n).sum fun i => c i := by
                apply Finset.sum_congr rfl
                intro i hi
                exact Nat.sub_add_cancel (hpos i hi)
  have hsum_le_total :
      (internalIndices n).sum (fun i => c i) ≤ total c := by
    simpa [total] using
      (Finset.sum_le_sum_of_subset_of_nonneg
        (s := internalIndices n) (t := Finset.univ) (f := c)
        (by intro i hi; simp)
        (by intro i hi hnot; exact Nat.zero_le (c i)))
  have hcard := card_internalIndices n
  have hmain :
      (internalIndices n).sum (fun i => c i - 1) + (n - 2) ≤ n + 4 := by
    rw [← hcard, hadd]
    simpa [htotal] using hsum_le_total
  omega

private lemma exception_card_le_internal_excess {n : ℕ} {c : Counts n}
    (hpos : ∀ i ∈ internalIndices n, 1 ≤ c i) :
    ((internalIndices n).filter (fun i => c i ≠ 1)).card ≤
      (internalIndices n).sum (fun i => c i - 1) := by
  let E := (internalIndices n).filter (fun i => c i ≠ 1)
  have hEsubset : E ⊆ internalIndices n := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  calc
    E.card = E.sum (fun _ => 1) := by
      rw [Finset.card_eq_sum_ones]
    _ ≤ E.sum (fun i => c i - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_internal : i ∈ internalIndices n := hEsubset hi
      have hi_ne : c i ≠ 1 := (Finset.mem_filter.mp hi).2
      have hi_pos : 1 ≤ c i := hpos i hi_internal
      omega
    _ ≤ (internalIndices n).sum (fun i => c i - 1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hEsubset
        (by intro i hi hnot; exact Nat.zero_le (c i - 1))

private lemma seven_le_exception_card_of_no_three {n : ℕ} {c : Counts n}
    (hn24 : 24 ≤ n)
    (hno_three :
      ∀ j : ℕ, 1 ≤ j → j + 3 < n →
        ¬ (∀ r : Fin n, j ≤ r.val → r.val < j + 3 → c r = 1)) :
    7 ≤ ((internalIndices n).filter (fun i => c i ≠ 1)).card := by
  classical
  let E := (internalIndices n).filter (fun i => c i ≠ 1)
  have hblock :
      ∀ t : Fin 7,
        ∃ r : Fin n,
          (1 + 3 * t.val ≤ r.val ∧
            r.val < 1 + 3 * t.val + 3 ∧ c r ≠ 1) := by
    intro t
    let j := 1 + 3 * t.val
    have hj_left : 1 ≤ j := by omega
    have hj_right : j + 3 < n := by
      have ht : t.val < 7 := t.isLt
      omega
    by_contra hnone
    apply hno_three j hj_left hj_right
    intro r hrL hrR
    by_contra hr_ne
    exact hnone ⟨r, hrL, hrR, hr_ne⟩
  let pick : Fin 7 → Fin n := fun t => Classical.choose (hblock t)
  have pick_spec :
      ∀ t : Fin 7,
        1 + 3 * t.val ≤ (pick t).val ∧
          (pick t).val < 1 + 3 * t.val + 3 ∧ c (pick t) ≠ 1 := by
    intro t
    exact Classical.choose_spec (hblock t)
  have hpick_mem : ∀ t : Fin 7, pick t ∈ E := by
    intro t
    have ht := pick_spec t
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_internalIndices.mpr
      constructor <;> omega
    · exact ht.2.2
  have hpick_inj : Function.Injective pick := by
    intro t u htu
    apply Fin.ext
    have ht := pick_spec t
    have hu := pick_spec u
    have hval : (pick t).val = (pick u).val := congrArg Fin.val htu
    omega
  let S : Finset (Fin n) := (Finset.univ : Finset (Fin 7)).image pick
  have hS_card : S.card = 7 := by
    rw [Finset.card_image_of_injective _ hpick_inj]
    simp
  have hS_subset : S ⊆ E := by
    intro i hi
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hi
    rcases hi with ⟨t, rfl⟩
    exact hpick_mem t
  have hcard_le : S.card ≤ E.card := Finset.card_le_card hS_subset
  have hE_eq :
      E.card = ((internalIndices n).filter (fun i => c i ≠ 1)).card := by
    rfl
  omega

/-- Any counterexample at an admissible size yields one at a size in `smallSizes`. -/
theorem counterexample_size_bound
    (h : ∃ n, 6 ≤ n ∧ 3 ∣ n ∧ CounterexampleAt n) :
    ∃ n₀, n₀ ∈ smallSizes ∧ CounterexampleAt n₀ := by
  classical
  let P : ℕ → Prop := fun m => 6 ≤ m ∧ 3 ∣ m ∧ CounterexampleAt m
  have hP : ∃ m, P m := by
    simpa [P] using h
  let n := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  have hminimal : ∀ {m : ℕ}, m < n → ¬ P m := by
    intro m hm
    exact Nat.find_min hP hm
  rcases hnP with ⟨hn6, hdiv, hcounter⟩
  rcases hcounter with ⟨c, hc, hnonstd⟩
  by_cases hn22 : n ≤ 22
  · exact ⟨n, smallSizes_mem_of_admissible_le_22 hn6 hdiv hn22, ⟨c, hc, hnonstd⟩⟩
  · have hn24 : 24 ≤ n := by
      have hn23 : 23 ≤ n := by omega
      rcases hdiv with ⟨k, hk⟩
      omega
    have hn9 : 9 ≤ n := by omega
    have hno_three :
        ∀ j : ℕ, 1 ≤ j → j + 3 < n →
          ¬ (∀ r : Fin n, j ≤ r.val → r.val < j + 3 → c r = 1) := by
      intro j hj_left hj_right hsingle
      let hj : j + 3 ≤ n := Nat.le_of_lt hj_right
      let d : Counts (n - 3) := deleteThree c j hj
      have hd_live : LiveWait d := by
        dsimp [d, hj]
        exact delete_three_live_wait hn9 hdiv c hc j hj_left hj_right hsingle
      by_cases hd_std : d = standard (n - 3)
      · have hc_std : c = standard n := by
          exact (delete_three_standard_iff c j hj_left hj_right hsingle).mpr
            (by simpa [d, hj] using hd_std)
        exact hnonstd hc_std
      · have hdiv_del : 3 ∣ n - 3 := by
          rcases hdiv with ⟨k, hk⟩
          exact ⟨k - 1, by omega⟩
        have hPdel : P (n - 3) := by
          refine ⟨by omega, hdiv_del, ?_⟩
          exact ⟨d, hd_live, hd_std⟩
        exact (hminimal (by omega)) hPdel
    have hpos :
        ∀ i ∈ internalIndices n, 1 ≤ c i := by
      intro i hi
      have hi' := mem_internalIndices.mp hi
      exact interior_positive hn6 hdiv hc hi'.1 hi'.2
    have hexcess_le : (internalIndices n).sum (fun i => c i - 1) ≤ 6 :=
      internal_excess_le_six hn6 hdiv hc
    have hcard_le :
        ((internalIndices n).filter (fun i => c i ≠ 1)).card ≤
          (internalIndices n).sum (fun i => c i - 1) :=
      exception_card_le_internal_excess hpos
    have hseven :
        7 ≤ ((internalIndices n).filter (fun i => c i ≠ 1)).card :=
      seven_le_exception_card_of_no_three hn24 hno_three
    omega

/-- Excluding counterexamples at all sizes in `smallSizes` excludes them globally. -/
theorem no_counterexample_of_small
    (hsmall : ∀ n ∈ smallSizes, ¬ CounterexampleAt n) :
    ∀ n, 6 ≤ n → 3 ∣ n → ¬ CounterexampleAt n := by
  intro n hn6 hdiv hcounter
  rcases counterexample_size_bound ⟨n, hn6, hdiv, hcounter⟩ with
    ⟨n₀, hn₀_small, hn₀_counter⟩
  exact hsmall n₀ hn₀_small hn₀_counter

end Ninegates
