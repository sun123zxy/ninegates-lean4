import NinegatesFormalization.Positivity
import NinegatesFormalization.Standard

namespace Mahjong.Hand

variable {n : ℕ}

def insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) : Hand (n + 1) :=
  Fin.insertNth k.castSucc.castSucc 1 <|
    Fin.insertNth k.castSucc 1 <|
      Fin.insertNth k 1 c

@[simp]
lemma insertSeqAt_apply_zero (c : Hand n) (k : Fin (3 * n + 1)) :
    c.insertSeqAt k k.castSucc.castSucc = 1 := by
  simp [insertSeqAt]

@[simp]
lemma insertSeqAt_apply_one (c : Hand n) (k : Fin (3 * n + 1)) :
    c.insertSeqAt k k.succ.castSucc = 1 := by
  unfold insertSeqAt
  have hpos : k.succ.castSucc =
      k.castSucc.castSucc.succAbove k.castSucc := by
    ext
    simp [Fin.succAbove]
  rw [hpos, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]

@[simp]
lemma insertSeqAt_apply_two (c : Hand n) (k : Fin (3 * n + 1)) :
    c.insertSeqAt k k.succ.succ = 1 := by
  unfold insertSeqAt
  have hnot : ¬k.castSucc.succ < k.castSucc.castSucc := by
    change ¬k.val + 1 < k.val
    omega
  have hpos₂ : k.succ.succ =
      k.castSucc.castSucc.succAbove k.succ := by
    ext
    simp [Fin.succAbove, hnot]
  have hpos₁ : k.succ = k.castSucc.succAbove k := by
    ext
    simp [Fin.succAbove]
  rw [hpos₂, Fin.insertNth_apply_succAbove,
    hpos₁, Fin.insertNth_apply_succAbove]
  exact @Fin.insertNth_apply_same _ (fun _ ↦ ℕ) k 1 c

theorem Meldable.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Meldable (c.insertSeqAt k)) : Meldable c := by
  sorry

theorem IsFullWait.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : IsFullWait (c.insertSeqAt k)) : IsFullWait c := by
  sorry

private theorem insertSeqAt_standardFullWait
    (k : Fin (3 * n + 1)) (hk₀ : 0 < k.val) (hk₁ : k.val < 3 * n) :
    (standardFullWait n).insertSeqAt k = standardFullWait (n + 1) := by
  unfold insertSeqAt Hand standardFullWait
  rw [Fin.insertNth_eq_iff]
  constructor
  · change 1 = if k.val = 0 ∨ k.val + 1 = 3 * (n + 1) then 3 else 1
    have hzero : k.val ≠ 0 := by omega
    have hlast : k.val + 1 ≠ 3 * (n + 1) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    simp [hzero, hlast]
  · rw [Fin.insertNth_eq_iff]
    constructor
    · rw [Fin.removeNth_apply,
        Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
      change 1 = if k.val + 1 = 0 ∨ k.val + 2 = 3 * (n + 1) then 3 else 1
      have hlast : k.val + 2 ≠ 3 * (n + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      simp [hlast]
    · rw [Fin.insertNth_eq_iff]
      constructor
      · rw [Fin.removeNth_apply,
          Fin.succAbove_of_le_castSucc _ _ (le_refl _),
          Fin.removeNth_apply]
        have hle : k.castSucc.castSucc ≤ k.succ.castSucc := by
          apply Fin.mk_le_mk.mpr
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        simp only [Fin.val_succ]
        change 1 = if k.val + 2 = 0 ∨ k.val + 3 = 3 * (n + 1) then 3 else 1
        have hlast : k.val + 3 ≠ 3 * (n + 1) := by
          simp only [Nat.mul_add, Nat.mul_one]
          omega
        simp [hlast]
      · funext i
        rw [Fin.removeNth_apply, Fin.removeNth_apply, Fin.removeNth_apply]
        by_cases hi : i.val < k.val
        · have h₀ : i.castSucc < k := by
            apply Fin.mk_lt_mk.mpr
            simpa only [Fin.val_castSucc] using hi
          rw [Fin.succAbove_of_castSucc_lt _ _ h₀]
          have h₁ : i.castSucc.castSucc < k.castSucc := by
            apply Fin.mk_lt_mk.mpr
            simpa only [Fin.val_castSucc] using hi
          rw [Fin.succAbove_of_castSucc_lt _ _ h₁]
          have h₂ : i.castSucc.castSucc.castSucc <
              k.castSucc.castSucc := by
            apply Fin.mk_lt_mk.mpr
            simpa only [Fin.val_castSucc] using hi
          rw [Fin.succAbove_of_castSucc_lt _ _ h₂]
          change (if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1) =
            if i.val = 0 ∨ i.val + 1 = 3 * (n + 1) then 3 else 1
          by_cases hz : i.val = 0
          · simp [hz]
          · have hlast : i.val + 1 ≠ 3 * n := by omega
            have hbig : i.val + 1 ≠ 3 * (n + 1) := by
              have hil := i.isLt
              simp only [Nat.mul_add, Nat.mul_one]
              omega
            simp [hz, hlast, hbig]
        · have h₀ : k ≤ i.castSucc := by
            apply Fin.mk_le_mk.mpr
            simpa only [Fin.val_castSucc] using Nat.le_of_not_gt hi
          rw [Fin.succAbove_of_le_castSucc _ _ h₀]
          have h₁ : k.castSucc ≤ i.succ.castSucc := by
            apply Fin.mk_le_mk.mpr
            simp only [Fin.val_succ]
            omega
          rw [Fin.succAbove_of_le_castSucc _ _ h₁]
          have h₂ : k.castSucc.castSucc ≤ i.succ.succ.castSucc := by
            apply Fin.mk_le_mk.mpr
            simp only [Fin.val_castSucc, Fin.val_succ]
            omega
          rw [Fin.succAbove_of_le_castSucc _ _ h₂]
          change (if i.val = 0 ∨ i.val + 1 = 3 * n then 3 else 1) =
            if i.val + 3 = 0 ∨ i.val + 4 = 3 * (n + 1) then 3 else 1
          have hz : i.val ≠ 0 := by omega
          by_cases hlast : i.val + 1 = 3 * n
          · rw [if_pos (Or.inr hlast)]
            have hbig : i.val + 4 = 3 * (n + 1) := by
              simp only [Nat.mul_add, Nat.mul_one]
              omega
            rw [if_pos (Or.inr hbig)]
          · rw [if_neg (by omega)]
            have hbig : i.val + 4 ≠ 3 * (n + 1) := by
              simp only [Nat.mul_add, Nat.mul_one]
              omega
            rw [if_neg (by omega)]

private theorem exists_insertSeqAt_of_large
    (hn : 6 < n) {c : Hand (n + 1)} (hc : IsFullWait c) :
    ∃ d : Hand n, ∃ k : Fin (3 * n + 1),
      0 < k.val ∧ k.val < 3 * n ∧ c = d.insertSeqAt k := by
  let idx : Fin (3 * n + 1) → Fin (3 * (n + 1)) :=
    fun i ↦ ⟨i.val + 1, by
      simp only [Nat.mul_add, Nat.mul_one]
      omega⟩
  have hpositive (i : Fin (3 * n + 1)) : 0 < c (idx i) := by
    apply interior_positive (n := n + 1) (by omega) c hc
    constructor
    · simp [idx]
    · simp only [idx, Nat.mul_add, Nat.mul_one]
      omega
  have hsum_le :
      (∑ i : Fin (3 * n + 1), c (idx i)) ≤ size c := by
    change (∑ i : Fin (3 * n + 1), c (idx i)) ≤
      ∑ j : Fin (3 * (n + 1)), c j
    have hinj : Function.Injective idx := by
      intro i j hij
      apply Fin.ext
      have := congrArg Fin.val hij
      simp only [idx] at this
      omega
    calc
      (∑ i : Fin (3 * n + 1), c (idx i)) =
          ∑ j ∈ Finset.univ.image idx, c j := by
        symm
        exact Finset.sum_image hinj.injOn
      _ ≤ ∑ j : Fin (3 * (n + 1)), c j := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.subset_univ _
  have hdecomp :
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i) - 1) =
        ∑ i : Fin (3 * n + 1), c (idx i) := by
    have hones : (∑ _ : Fin (3 * n + 1), 1) = 3 * n + 1 := by simp
    calc
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i) - 1) =
          (∑ _ : Fin (3 * n + 1), 1) +
            ∑ i : Fin (3 * n + 1), (c (idx i) - 1) := by rw [hones]
      _ = ∑ i : Fin (3 * n + 1), (1 + (c (idx i) - 1)) :=
        Finset.sum_add_distrib.symm
      _ = ∑ i : Fin (3 * n + 1), c (idx i) := by
        apply Finset.sum_congr rfl
        intro i _
        have := hpositive i
        omega
  have hexcess :
      (∑ i : Fin (3 * n + 1), (c (idx i) - 1)) ≤ 6 := by
    have hsize := hc.size (by omega)
    rw [← hdecomp] at hsum_le
    rw [hsize] at hsum_le
    simp only [Nat.mul_add, Nat.mul_one] at hsum_le
    omega
  let block : Fin 7 → Fin 3 → Fin (3 * n + 1) :=
    fun a b ↦ ⟨3 * a.val + b.val, by omega⟩
  have hblock :
      ∃ a : Fin 7, ∀ b : Fin 3, c (idx (block a b)) - 1 = 0 := by
    by_contra h
    push Not at h
    have hone (a : Fin 7) :
        1 ≤ ∑ b : Fin 3, (c (idx (block a b)) - 1) := by
      obtain ⟨b, hb⟩ := h a
      calc
        1 ≤ c (idx (block a b)) - 1 := Nat.one_le_iff_ne_zero.mpr hb
        _ ≤ ∑ b : Fin 3, (c (idx (block a b)) - 1) := by
          have hsingle := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun b : Fin 3 ↦ c (idx (block a b)) - 1)
            (by simp) (Finset.mem_univ b)
          simpa using hsingle
    have hseven :
        7 ≤ ∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)) - 1) := by
      have hsum := Finset.sum_le_sum
        (s := Finset.univ) (f := fun _ : Fin 7 ↦ 1)
        (g := fun a ↦ ∑ b : Fin 3, (c (idx (block a b)) - 1))
        (by
          intro a _
          exact hone a)
      simpa using hsum
    have hblocks_le :
        (∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)) - 1)) ≤
            ∑ i : Fin (3 * n + 1), (c (idx i) - 1) := by
      let pairIdx : Fin 7 × Fin 3 → Fin (3 * n + 1) :=
        fun x ↦ block x.1 x.2
      have hinj : Function.Injective pairIdx := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        have hv := congrArg Fin.val hab
        simp only [pairIdx, block] at hv
        have hb := b.isLt
        have hb' := b'.isLt
        have ha : a.val = a'.val := by omega
        have hbb : b.val = b'.val := by omega
        have haa : a = a' := Fin.ext ha
        have hbbb : b = b' := Fin.ext hbb
        cases haa
        cases hbbb
        rfl
      calc
        (∑ a : Fin 7, ∑ b : Fin 3,
            (c (idx (block a b)) - 1)) =
            ∑ x : Fin 7 × Fin 3, (c (idx (pairIdx x)) - 1) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ i ∈ Finset.univ.image pairIdx, (c (idx i) - 1) := by
          symm
          exact Finset.sum_image hinj.injOn
        _ ≤ ∑ i : Fin (3 * n + 1), (c (idx i) - 1) := by
          apply Finset.sum_le_sum_of_subset
          exact Finset.subset_univ _
    omega
  obtain ⟨a, ha⟩ := hblock
  let k : Fin (3 * n + 1) := ⟨3 * a.val + 1, by omega⟩
  have hk₀ : 0 < k.val := by simp [k]
  have hk₁ : k.val < 3 * n := by simp [k]; omega
  have hc₀ : c k.castSucc.castSucc = 1 := by
    have hv := ha (0 : Fin 3)
    have hp := hpositive (block a 0)
    have heq : k.castSucc.castSucc = idx (block a 0) := by
      apply Fin.ext
      simp [k, idx, block]
    rw [heq]
    omega
  have hc₁ : c k.succ.castSucc = 1 := by
    have hv := ha (1 : Fin 3)
    have hp := hpositive (block a 1)
    have heq : k.succ.castSucc = idx (block a 1) := by
      apply Fin.ext
      simp [k, idx, block]
    rw [heq]
    omega
  have hc₂ : c k.succ.succ = 1 := by
    have hv := ha (2 : Fin 3)
    have hp := hpositive (block a 2)
    have heq : k.succ.succ = idx (block a 2) := by
      apply Fin.ext
      simp [k, idx, block]
    rw [heq]
    omega
  let d : Hand n :=
    Fin.removeNth k <|
      Fin.removeNth k.castSucc <|
        Fin.removeNth k.castSucc.castSucc c
  refine ⟨d, k, hk₀, hk₁, ?_⟩
  symm
  unfold insertSeqAt d Hand
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · exact hc₀.symm
  · apply Fin.insertNth_eq_iff.mpr
    constructor
    · change 1 = c (k.castSucc.castSucc.succAbove k.castSucc)
      rw [Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
      exact hc₁.symm
    · apply Fin.insertNth_eq_iff.mpr
      constructor
      · change 1 = c
          (k.castSucc.castSucc.succAbove (k.castSucc.succAbove k))
        rw [Fin.succAbove_of_le_castSucc _ _ (le_refl _)]
        have hle : k.castSucc.castSucc ≤ k.succ.castSucc := by
          apply Fin.mk_le_mk.mpr
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        exact hc₂.symm
      · rfl

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
