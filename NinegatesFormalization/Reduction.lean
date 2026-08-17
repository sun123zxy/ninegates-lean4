import NinegatesFormalization.Positivity
import NinegatesFormalization.Standard

namespace Mahjong.Hand

variable {n : ℕ}

private def insertSeqAt' (c : Hand n) (k : Fin (3 * n + 1)) :
    Fin (3 * n + 3) → ℕ :=
  Fin.insertNth k.castSucc.castSucc 1 <|
    Fin.insertNth k.castSucc 1 <| Fin.insertNth k 1 fun i ↦ c i.val

def insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) : Hand (n + 1) :=
  Hand.ofFn (insertSeqAt' c k)

@[simp]
private lemma insertSeqAt_apply (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * n + 3)) : c.insertSeqAt k i.val = insertSeqAt' c k i := by
  simp only [insertSeqAt, Hand.ofFn_apply]
  split
  · simp only [Int.toNat_natCast]
    congr
  · omega

@[simp]
lemma insertSeqAt_apply_zero (c : Hand n) (k : Fin (3 * n + 1)) :
    c.insertSeqAt k k.castSucc.castSucc.val = 1 := by
  calc
    c.insertSeqAt k k.castSucc.castSucc.val =
        insertSeqAt' c k k.castSucc.castSucc := insertSeqAt_apply c k _
    _ = 1 := by simp [insertSeqAt']

@[simp]
lemma insertSeqAt_apply_one (c : Hand n) (k : Fin (3 * n + 1)) :
    c.insertSeqAt k k.succ.castSucc.val = 1 := by
  simp only [insertSeqAt_apply]
  unfold insertSeqAt'
  have hpos : k.succ.castSucc =
      k.castSucc.castSucc.succAbove k.castSucc := by
    grind [Fin.succAbove]
  rw [hpos, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]

@[simp]
lemma insertSeqAt_apply_two (c : Hand n) (k : Fin (3 * n + 1)) :
    c.insertSeqAt k k.succ.succ.val = 1 := by
  simp only [insertSeqAt_apply]
  unfold insertSeqAt'
  have hnot : ¬k.castSucc.succ < k.castSucc.castSucc := by grind
  have hpos₂ : k.succ.succ =
      k.castSucc.castSucc.succAbove k.succ := by
    grind [Fin.succAbove, hnot]
  have hpos₁ : k.succ = k.castSucc.succAbove k := by
    grind [Fin.succAbove]
  rw [hpos₂, Fin.insertNth_apply_succAbove,
    hpos₁, Fin.insertNth_apply_succAbove]
  exact @Fin.insertNth_apply_same _ (fun _ ↦ ℕ) k 1 (fun i ↦ c i.val)

theorem Meldable.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Meldable (c.insertSeqAt k)) : Meldable c := by
  sorry

theorem IsFullWait.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : IsFullWait (c.insertSeqAt k)) : IsFullWait c := by
  sorry

private theorem insertSeqAt_standardFullWait
    (k : Fin (3 * n + 1)) (hk₀ : 0 < k.val) (hk₁ : k.val < 3 * n) :
    (standardFullWait n).insertSeqAt k = standardFullWait (n + 1) := by
  unfold insertSeqAt insertSeqAt' standardFullWait
  apply congrArg Hand.ofFn
  rw [Fin.insertNth_eq_iff]
  constructor
  · change 1 = if k.val = 0 ∨ k.val + 1 = 3 * (n + 1) then 3 else 1
    grind
  · rw [Fin.insertNth_eq_iff]
    constructor
    · rw [Fin.removeNth_apply,
        Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
      change 1 = if k.val + 1 = 0 ∨ k.val + 2 = 3 * (n + 1) then 3 else 1
      grind
    · rw [Fin.insertNth_eq_iff]
      constructor
      · rw [Fin.removeNth_apply,
          Fin.succAbove_of_le_castSucc _ _ (le_refl _),
          Fin.removeNth_apply]
        have hle : k.castSucc.castSucc ≤ k.succ.castSucc := by grind
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        grind
      · funext i
        rw [Fin.removeNth_apply, Fin.removeNth_apply, Fin.removeNth_apply]
        by_cases hi : i.val < k.val
        · have h₀ : i.castSucc < k := by grind
          rw [Fin.succAbove_of_castSucc_lt _ _ h₀]
          have h₁ : i.castSucc.castSucc < k.castSucc := by grind
          rw [Fin.succAbove_of_castSucc_lt _ _ h₁]
          have h₂ : i.castSucc.castSucc.castSucc <
              k.castSucc.castSucc := by grind
          rw [Fin.succAbove_of_castSucc_lt _ _ h₂]
          grind
        · have h₀ : k ≤ i.castSucc := by grind
          rw [Fin.succAbove_of_le_castSucc _ _ h₀]
          have h₁ : k.castSucc ≤ i.succ.castSucc := by grind
          rw [Fin.succAbove_of_le_castSucc _ _ h₁]
          have h₂ : k.castSucc.castSucc ≤ i.succ.succ.castSucc := by grind
          rw [Fin.succAbove_of_le_castSucc _ _ h₂]
          grind

private theorem exists_insertSeqAt_of_large
    (hn : 6 < n) {c : Hand (n + 1)} (hc : IsFullWait c) :
    ∃ d : Hand n, ∃ k : Fin (3 * n + 1),
      0 < k.val ∧ k.val < 3 * n ∧ c = d.insertSeqAt k := by
  let idx : Fin (3 * n + 1) → Fin (3 * (n + 1)) :=
    fun i ↦ ⟨i.val + 1, by omega⟩
  have hpositive (i : Fin (3 * n + 1)) : 0 < c (idx i).val := by
    apply interior_positive (n := n + 1) (by omega) c hc
    grind
  have hsum_le :
      (∑ i : Fin (3 * n + 1), c (idx i).val) ≤ size c := by
    change (∑ i : Fin (3 * n + 1), c (idx i).val) ≤
      ∑ j : Fin (3 * (n + 1)), c j.val
    have hinj : Function.Injective idx := by
      intro i j hij
      have hval := congrArg Fin.val hij
      grind
    calc
      (∑ i : Fin (3 * n + 1), c (idx i).val) =
          ∑ j ∈ Finset.univ.image idx, c j.val := by
        symm
        exact Finset.sum_image hinj.injOn
      _ ≤ ∑ j : Fin (3 * (n + 1)), c j.val := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.subset_univ _
  have hdecomp :
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) =
        ∑ i : Fin (3 * n + 1), c (idx i).val := by
    have hones : (∑ _ : Fin (3 * n + 1), 1) = 3 * n + 1 := by simp
    calc
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) =
          (∑ _ : Fin (3 * n + 1), 1) +
            ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) := by rw [hones]
      _ = ∑ i : Fin (3 * n + 1), (1 + (c (idx i).val - 1)) :=
        Finset.sum_add_distrib.symm
      _ = ∑ i : Fin (3 * n + 1), c (idx i).val := by
        apply Finset.sum_congr rfl
        intro i _
        have := hpositive i
        omega
  have hexcess :
      (∑ i : Fin (3 * n + 1), (c (idx i).val - 1)) ≤ 6 := by
    have hsize := hc.size (by omega)
    rw [← hdecomp] at hsum_le
    rw [hsize] at hsum_le
    simp only [Nat.mul_add, Nat.mul_one] at hsum_le
    omega
  let block : Fin 7 → Fin 3 → Fin (3 * n + 1) :=
    fun a b ↦ ⟨3 * a.val + b.val, by omega⟩
  have hblock :
      ∃ a : Fin 7, ∀ b : Fin 3, c (idx (block a b)).val - 1 = 0 := by
    by_contra h
    push Not at h
    have hone (a : Fin 7) :
        1 ≤ ∑ b : Fin 3, (c (idx (block a b)).val - 1) := by
      obtain ⟨b, hb⟩ := h a
      calc
        1 ≤ c (idx (block a b)).val - 1 := Nat.one_le_iff_ne_zero.mpr hb
        _ ≤ ∑ b : Fin 3, (c (idx (block a b)).val - 1) := by
          have hsingle := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun b : Fin 3 ↦ c (idx (block a b)).val - 1)
            (by simp) (Finset.mem_univ b)
          simpa using hsingle
    have hseven :
        7 ≤ ∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)).val - 1) := by
      have hsum := Finset.sum_le_sum
        (s := Finset.univ) (f := fun _ : Fin 7 ↦ 1)
        (g := fun a ↦ ∑ b : Fin 3, (c (idx (block a b)).val - 1))
        (by
          intro a _
          exact hone a)
      simpa using hsum
    have hblocks_le :
        (∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)).val - 1)) ≤
            ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) := by
      let pairIdx : Fin 7 × Fin 3 → Fin (3 * n + 1) :=
        fun x ↦ block x.1 x.2
      have hinj : Function.Injective pairIdx := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        have hv := congrArg Fin.val hab
        grind
      calc
        (∑ a : Fin 7, ∑ b : Fin 3,
            (c (idx (block a b)).val - 1)) =
            ∑ x : Fin 7 × Fin 3, (c (idx (pairIdx x)).val - 1) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ i ∈ Finset.univ.image pairIdx, (c (idx i).val - 1) := by
          symm
          exact Finset.sum_image hinj.injOn
        _ ≤ ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) := by
          apply Finset.sum_le_sum_of_subset
          exact Finset.subset_univ _
    omega
  obtain ⟨a, ha⟩ := hblock
  let k : Fin (3 * n + 1) := ⟨3 * a.val + 1, by omega⟩
  have hk₀ : 0 < k.val := by grind
  have hk₁ : k.val < 3 * n := by grind
  have hc (b : Fin 3) : c (idx (block a b)).val = 1 := by
    have hv := ha b
    have hp := hpositive (block a b)
    grind
  have hc₀ : c k.castSucc.castSucc.val = 1 := by simpa [k, idx, block] using hc 0
  have hc₁ : c k.succ.castSucc.val = 1 := by simpa [k, idx, block] using hc 1
  have hc₂ : c k.succ.succ.val = 1 := by
    have hidx : (idx (block a 2)).val = k.succ.succ.val := by grind
    grind
  let d : Hand n :=
    Hand.ofFn <| Fin.removeNth k <|
      Fin.removeNth k.castSucc <|
        Fin.removeNth k.castSucc.castSucc fun i ↦ c i.val
  refine ⟨d, k, hk₀, hk₁, ?_⟩
  symm
  unfold insertSeqAt d
  trans Hand.ofFn fun i ↦ c i.val
  · apply congrArg Hand.ofFn
    apply Fin.insertNth_eq_iff.mpr
    constructor
    · exact hc₀.symm
    · apply Fin.insertNth_eq_iff.mpr
      constructor
      · change 1 = c (k.castSucc.castSucc.succAbove k.castSucc).val
        rw [Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
        exact hc₁.symm
      · apply Fin.insertNth_eq_iff.mpr
        constructor
        · change 1 = c
            (k.castSucc.castSucc.succAbove (k.castSucc.succAbove k)).val
          rw [Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
          have hle : k.castSucc.castSucc ≤ k.succ.castSucc := by grind
          rw [Fin.succAbove_of_le_castSucc _ _ hle]
          exact hc₂.symm
        · funext i
          simp
          rfl
  · apply Hand.ext
    intro i hi₀ hi₁
    simp only [Hand.ofFn_apply]
    split <;> grind

abbrev IsCounterexample (c : Hand n) : Prop :=
  IsFullWait c ∧ c ≠ standardFullWait n

theorem full_wait_reduction {n : ℕ} (hn : 2 ≤ n) {c : Hand n}
    (hc : IsCounterexample c) :
    ∃ m, 2 ≤ m ∧ m ≤ 7 ∧ ∃ d : Hand m, IsCounterexample d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n ≤ 7
      · exact ⟨n, hn, hsmall, c, hc⟩
      · cases n with
        | zero => omega
        | succ m =>
            obtain ⟨d, k, hk₀, hk₁, hcd⟩ :=
              exists_insertSeqAt_of_large (n := m) (by omega) hc.1
            have hdFull : IsFullWait d :=
              IsFullWait.of_insertSeqAt k (hcd ▸ hc.1)
            have hdNe : d ≠ standardFullWait m := by
              intro hd
              apply hc.2
              calc
                c = d.insertSeqAt k := hcd
                _ = (standardFullWait m).insertSeqAt k := by rw [hd]
                _ = standardFullWait (m + 1) :=
                  insertSeqAt_standardFullWait k hk₀ hk₁
            exact ih m (by omega) (by omega) ⟨hdFull, hdNe⟩

end Mahjong.Hand
