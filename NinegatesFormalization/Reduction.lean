import NinegatesFormalization.Positivity
import NinegatesFormalization.Standard

namespace Mahjong.Hand

variable {n : ℕ}

def insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) : Hand (n + 1) :=
  Hand.ofFn fun i ↦
    if (i.val : ℤ) < k.val then c i.val
    else if (i.val : ℤ) < k.val + 3 then 1
    else c ((i.val : ℤ) - 3)

@[grind =]
lemma insertSeqAt_apply (c : Hand n) (k : Fin (3 * n + 1)) (i : ℤ) :
    c.insertSeqAt k i =
      if i < k.val then c i
      else if i < k.val + 3 then 1
      else c (i - 3) := by
  simp only [insertSeqAt, Hand.ofFn_apply]
  split <;> grind

@[grind =] private lemma size_insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) :
    size (c.insertSeqAt k) = size c + 3 := by
  sorry

private def removeSeqAt (c : Hand (n + 1)) (k : Fin (3 * n + 1)) : Hand n :=
  Hand.ofFn fun i ↦
    if (i.val : ℤ) < k.val then c i.val else c ((i.val : ℤ) + 3)

private lemma insertSeqAt_removeSeqAt (c : Hand (n + 1))
    (k : Fin (3 * n + 1)) (h₀ : c k.val = 1)
    (h₁ : c (↑(k.val + 1) : ℤ) = 1) (h₂ : c (↑(k.val + 2) : ℤ) = 1) :
    (removeSeqAt c k).insertSeqAt k = c := by
  apply Hand.ext
  intro i hi₀ hi₁
  simp only [insertSeqAt_apply, removeSeqAt, Hand.ofFn_apply]
  split <;> grind

theorem Meldable.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Meldable (c.insertSeqAt k)) : Meldable c := by
  sorry

theorem Winning.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Winning (c.insertSeqAt k)) : Winning c := by
  rcases hc with ⟨hcvalid, hcsize, d, j, hd, hcd⟩
  have hvalid : Valid c := by
    intro i
    let j' : Fin (3 * (n + 1)) :=
      ⟨if i.val < k.val then i.val else i.val + 3, by split <;> omega⟩
    have h := hcvalid j'
    simp only [insertSeqAt_apply] at h
    split at h <;> grind
  have hsize : Hand.size c = 3 * n + 5 := by
    grind
  have hj : j.val < k.val ∨ k.val + 3 ≤ j.val := by
    by_contra h
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z j.val) hcd
    simp only [insertSeqAt_apply] at hEq
    split at hEq <;> grind
  have hd₀ : d k.val = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z k.val) hcd
    simp only [insertSeqAt_apply] at hEq
    split at hEq <;> grind
  have hd₁ : d (↑(k.val + 1) : ℤ) = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z (k.val + 1)) hcd
    simp only [insertSeqAt_apply] at hEq
    split at hEq <;> grind
  have hd₂ : d (↑(k.val + 2) : ℤ) = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z (k.val + 2)) hcd
    simp only [insertSeqAt_apply] at hEq
    split at hEq <;> grind
  have hdEq : (removeSeqAt d k).insertSeqAt k = d :=
    insertSeqAt_removeSeqAt d k hd₀ hd₁ hd₂
  have hd' : Meldable (removeSeqAt d k) := by
    apply Meldable.of_insertSeqAt k
    simpa only [hdEq] using hd
  let j' : Fin (3 * n) :=
    ⟨if j.val < k.val then j.val else j.val - 3, by split <;> omega⟩
  have htarget : c = removeSeqAt d k + pair j' := by
    apply Hand.ext
    intro x hx₀ hx₁
    by_cases hx : x < k.val
    · have hEq := congrArg (fun z : Hand (n + 1) ↦ z x) hcd
      simp [insertSeqAt_apply, removeSeqAt, pair_apply, j', hx] at hEq ⊢
      grind
    · have hEq := congrArg (fun z : Hand (n + 1) ↦ z (x + 3)) hcd
      simp [insertSeqAt_apply, removeSeqAt, pair_apply, j', hx] at hEq ⊢
      grind
  exact ⟨hvalid, hsize, removeSeqAt d k, j', hd', htarget⟩

theorem IsFullWait.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : IsFullWait (c.insertSeqAt k)) : IsFullWait c := by
  intro i
  let j : Fin (3 * (n + 1)) :=
    ⟨if i.val < k.val then i.val else i.val + 3, by split <;> omega⟩
  have hcomm : (c + single i).insertSeqAt k =
      c.insertSeqAt k + single j := by
    apply Hand.ext
    intro x hx₀ hx₁
    simp [insertSeqAt_apply, single_apply]
    split <;> grind
  exact Winning.of_insertSeqAt k (hcomm.symm ▸ hc j)

private lemma insertSeqAt_standardFullWait
    (k : Fin (3 * n + 1)) (hk₀ : 0 < k.val) (hk₁ : k.val < 3 * n) :
    (standardFullWait n).insertSeqAt k = standardFullWait (n + 1) := by
  apply Hand.ext
  intro i hi₀ hi₁
  simp only [insertSeqAt_apply, standardFullWait, Hand.ofFn_apply]
  split <;> grind

private lemma sum_comp_le_sum_of_injective
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (g : β → ℕ) :
    ∑ i, g (f i) ≤ ∑ j, g j := by
  classical
  calc
    ∑ i, g (f i) = ∑ j ∈ Finset.univ.image f, g j :=
      (Finset.sum_image hf.injOn).symm
    _ ≤ ∑ j, g j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem exists_insertSeqAt_of_large
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
    refine sum_comp_le_sum_of_injective idx ?_ (fun j ↦ c j.val)
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    grind
  have hdecomp :
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) =
        ∑ i : Fin (3 * n + 1), c (idx i).val := by
    calc
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i).val - 1) =
          ∑ i : Fin (3 * n + 1), (1 + (c (idx i).val - 1)) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin (3 * n + 1), c (idx i).val := by
        apply Finset.sum_congr rfl
        grind
  have hexcess :
      (∑ i : Fin (3 * n + 1), (c (idx i).val - 1)) ≤ 6 := by
    grind [IsFullWait.size]
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
        _ ≤ ∑ b : Fin 3, (c (idx (block a b)).val - 1) :=
          Finset.single_le_sum
            (f := fun b : Fin 3 ↦ c (idx (block a b)).val - 1)
            (by grind) (Finset.mem_univ b)
    have hseven :
        7 ≤ ∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)).val - 1) := by
      calc
        7 = ∑ _ : Fin 7, 1 := by simp
        _ ≤ ∑ a : Fin 7, ∑ b : Fin 3, (c (idx (block a b)).val - 1) :=
          Finset.sum_le_sum fun a _ ↦ hone a
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
      simpa only [Fintype.sum_prod_type] using
        sum_comp_le_sum_of_injective pairIdx hinj
          (fun i ↦ c (idx i).val - 1)
    omega
  obtain ⟨a, ha⟩ := hblock
  let k : Fin (3 * n + 1) := ⟨3 * a.val + 1, by omega⟩
  have hk₀ : 0 < k.val := by grind
  have hk₁ : k.val < 3 * n := by grind
  have hc (b : Fin 3) : c (idx (block a b)).val = 1 := by
    have hv := ha b
    have hp := hpositive (block a b)
    grind
  have hc₀ : c k.val = 1 := by simpa [k, idx, block] using hc 0
  have hc₁ : c (↑(k.val + 1) : ℤ) = 1 := by simpa [k, idx, block] using hc 1
  have hc₂ : c (↑(k.val + 2) : ℤ) = 1 := by
    have hi : (idx (block a 2)).val = k.val + 2 := by grind
    simpa only [hi] using hc 2
  exact ⟨removeSeqAt c k, k, hk₀, hk₁,
    (insertSeqAt_removeSeqAt c k hc₀ hc₁ hc₂).symm⟩

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
