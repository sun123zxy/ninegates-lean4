import NinegatesFormalization.Positivity
import NinegatesFormalization.Standard

namespace Mahjong.Hand

variable {n : ℕ}

def insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) : Hand (n + 1) :=
  ⟨fun i ↦
    if _h : i.val < k.val then c ⟨i.val, by omega⟩
    else if _h : i.val < k.val + 3 then 1
    else c ⟨i.val - 3, by omega⟩⟩

@[grind =]
lemma insertSeqAt_apply (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) :
    c.insertSeqAt k i =
      if _h : i.val < k.val then c ⟨i.val, by omega⟩
      else if _h : i.val < k.val + 3 then 1
      else c ⟨i.val - 3, by omega⟩ := rfl

@[simp, grind =]
lemma insertSeqAt_apply_of_lt (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) (hi : i.val < k.val) :
    c.insertSeqAt k i = c ⟨i.val, by omega⟩ := by grind

@[simp, grind =]
lemma insertSeqAt_apply_of_mem (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) (hi₀ : k.val ≤ i.val) (hi₁ : i.val < k.val + 3) :
    c.insertSeqAt k i = 1 := by grind

@[simp, grind =]
lemma insertSeqAt_apply_of_ge (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) (hi : k.val + 3 ≤ i.val) :
    c.insertSeqAt k i = c ⟨i.val - 3, by omega⟩ := by grind

def insertSeqEquiv (k : Fin (3 * n + 1)) :
    Fin (3 * n) ⊕ Fin 3 ≃ Fin (3 * (n + 1)) where
  toFun x := match x with
    | .inl i =>
        ⟨if i.val < k.val then i.val else i.val + 3, by split <;> omega⟩
    | .inr j => ⟨k.val + j.val, by omega⟩
  invFun i :=
    if h₀ : i.val < k.val then .inl ⟨i.val, by omega⟩
    else if h₁ : i.val < k.val + 3 then .inr ⟨i.val - k.val, by omega⟩
    else .inl ⟨i.val - 3, by omega⟩
  left_inv x := by
    rcases x with i | i
    · simp only
      by_cases hi : i.val < k.val
      · simp [hi]
      · simp [hi]
        omega
    · simp only
      have hk : ¬k.val + i.val < k.val := by omega
      have hki : k.val + i.val < k.val + 3 := by omega
      simp [hk, hki]
  right_inv i := by
    apply Fin.ext
    by_cases hi₀ : i.val < k.val
    · simp [hi₀]
    by_cases hi₁ : i.val < k.val + 3
    · simp [hi₀, hi₁]
      omega
    · have hi₂ : ¬i.val - 3 < k.val := by omega
      simp [hi₀, hi₁, hi₂]
      omega

@[simp, grind =]
lemma insertSeqEquiv_inl_val (k : Fin (3 * n + 1)) (i : Fin (3 * n)) :
    (insertSeqEquiv k (.inl i)).val =
      if i.val < k.val then i.val else i.val + 3 := rfl

@[simp, grind =]
lemma insertSeqEquiv_inr_val (k : Fin (3 * n + 1)) (i : Fin 3) :
    (insertSeqEquiv k (.inr i)).val = k.val + i.val := rfl

@[grind =]
lemma size_insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) :
    size (c.insertSeqAt k) = size c + 3 := by
  have hinl (i : Fin (3 * n)) :
      c.insertSeqAt k (insertSeqEquiv k (.inl i)) = c i := by
    simp only [insertSeqAt_apply, insertSeqEquiv_inl_val]
    split <;> grind
  have hinr (i : Fin 3) :
      c.insertSeqAt k (insertSeqEquiv k (.inr i)) = 1 := by
    simp only [insertSeqAt_apply, insertSeqEquiv_inr_val]
    grind
  change (∑ i : Fin (3 * (n + 1)), c.insertSeqAt k i) =
    (∑ i : Fin (3 * n), c i) + 3
  calc
    _ = ∑ x : Fin (3 * n) ⊕ Fin 3, c.insertSeqAt k (insertSeqEquiv k x) :=
      (Equiv.sum_comp (insertSeqEquiv k) (fun i ↦ c.insertSeqAt k i)).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [hinl, hinr]
      simp

def removeSeqAt (c : Hand (n + 1)) (k : Fin (3 * n + 1)) : Hand n :=
  ⟨fun i ↦
    if _h : i.val < k.val then c ⟨i.val, by omega⟩
    else c ⟨i.val + 3, by omega⟩⟩

@[grind =]
lemma removeSeqAt_apply (c : Hand (n + 1)) (k : Fin (3 * n + 1))
    (i : Fin (3 * n)) :
    removeSeqAt c k i =
      if _h : i.val < k.val then c ⟨i.val, by omega⟩
      else c ⟨i.val + 3, by omega⟩ := rfl

@[simp, grind =]
lemma removeSeqAt_apply_of_lt (c : Hand (n + 1)) (k : Fin (3 * n + 1))
    (i : Fin (3 * n)) (hi : i.val < k.val) :
    removeSeqAt c k i = c ⟨i.val, by omega⟩ := by grind

@[simp, grind =]
lemma removeSeqAt_apply_of_ge (c : Hand (n + 1)) (k : Fin (3 * n + 1))
    (i : Fin (3 * n)) (hi : k.val ≤ i.val) :
    removeSeqAt c k i = c ⟨i.val + 3, by omega⟩ := by grind

lemma insertSeqAt_removeSeqAt (c : Hand (n + 1))
    (k : Fin (3 * n + 1)) (h₀ : c ⟨k.val, by omega⟩ = 1)
    (h₁ : c ⟨k.val + 1, by omega⟩ = 1) (h₂ : c ⟨k.val + 2, by omega⟩ = 1) :
    (removeSeqAt c k).insertSeqAt k = c := by
  ext i
  grind

/- Note that this is a standalone proof. It does not rely on the scan algorithm. -/
theorem Meldable.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Meldable (c.insertSeqAt k)) : Meldable c := by
  rcases hc with ⟨p, hp⟩
  unfold Meldable.IsWitness at hp
  let k₀ : Fin (3 * (n + 1)) := ⟨k.val, by omega⟩
  let k₁ : Fin (3 * (n + 1)) := ⟨k.val + 1, by omega⟩
  let k₂ : Fin (3 * (n + 1)) := ⟨k.val + 2, by omega⟩
  have h₀ := congrArg (fun d : Hand (n + 1) ↦ d k₀) hp
  have h₁ := congrArg (fun d : Hand (n + 1) ↦ d k₁) hp
  have h₂ := congrArg (fun d : Hand (n + 1) ↦ d k₂) hp
  have hseq₁ (hk : 2 ≤ k.val) :
      p.seqNum k₁ = p.seqNum ⟨k.val - 2, by omega⟩ := by grind
  have hseq₂ (hk : 1 ≤ k.val) :
      p.seqNum k₂ = p.seqNum ⟨k.val - 1, by omega⟩ := by grind
  let q : Meldable.Placement n :=
    ⟨(fun i ↦
        if h : i.val < k.val then p.tripNum ⟨i.val, by omega⟩
        else p.tripNum ⟨i.val + 3, by omega⟩),
      (fun i ↦
        if h : i.val < k.val then p.seqNum ⟨i.val, by omega⟩
        else p.seqNum ⟨i.val + 3, by omega⟩), by
      constructor
      · intro i hi
        split
        · have hs₁ := hseq₁ (by omega)
          have hs₂ := hseq₂ (by omega)
          grind [Fin.ext]
        · apply Meldable.Placement.seqNum_of_ge
          simp only
          omega
      · intro i hi
        split
        · have hs₁ := hseq₁ (by omega)
          have hs₂ := hseq₂ (by omega)
          grind [Fin.ext]
        · apply Meldable.Placement.seqNum_of_ge
          simp only
          omega⟩
  refine ⟨q, ?_⟩
  unfold Meldable.IsWitness
  ext i
  simp only [q, Meldable.Placement.toHand_apply]
  by_cases hi : i.val < k.val
  · have hpi := congrArg
      (fun d : Hand (n + 1) ↦ d ⟨i.val, by omega⟩) hp
    simp only [Meldable.Placement.toHand_apply, insertSeqAt_apply] at hpi
    grind
  by_cases hi' : k.val + 2 ≤ i.val
  · have hpi := congrArg
      (fun d : Hand (n + 1) ↦ d ⟨i.val + 3, by omega⟩) hp
    simp only [Meldable.Placement.toHand_apply, insertSeqAt_apply] at hpi
    grind
  · have hpi := congrArg
      (fun d : Hand (n + 1) ↦ d ⟨i.val + 3, by omega⟩) hp
    simp only [Meldable.Placement.toHand_apply, insertSeqAt_apply] at hpi
    have hicases : i.val = k.val ∨ i.val = k.val + 1 := by omega
    rcases hicases with hik | hik <;> grind [Fin.ext]

theorem Winning.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Winning (c.insertSeqAt k)) : Winning c := by
  rcases hc with ⟨hcvalid, hcsize, d, j, hd, hcd⟩
  have hvalid : Valid c := by
    intro i
    let j' : Fin (3 * (n + 1)) :=
      ⟨if i.val < k.val then i.val else i.val + 3, by split <;> omega⟩
    have h := hcvalid j'
    grind
  have hsize : Hand.size c = 3 * n + 5 := by grind
  have hj : j.val < k.val ∨ k.val + 3 ≤ j.val := by
    by_contra h
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z j) hcd
    grind
  let k₀ : Fin (3 * (n + 1)) := ⟨k.val, by omega⟩
  let k₁ : Fin (3 * (n + 1)) := ⟨k.val + 1, by omega⟩
  let k₂ : Fin (3 * (n + 1)) := ⟨k.val + 2, by omega⟩
  have hd₀ : d k₀ = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z k₀) hcd
    grind
  have hd₁ : d k₁ = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z k₁) hcd
    grind
  have hd₂ : d k₂ = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z k₂) hcd
    grind
  have hdEq : (removeSeqAt d k).insertSeqAt k = d :=
    insertSeqAt_removeSeqAt d k hd₀ hd₁ hd₂
  have hd' : Meldable (removeSeqAt d k) := by
    apply Meldable.of_insertSeqAt k
    simpa only [hdEq] using hd
  let j' : Fin (3 * n) :=
    ⟨if j.val < k.val then j.val else j.val - 3, by split <;> omega⟩
  have htarget : c = removeSeqAt d k + pair j' := by
    ext x
    by_cases hx : x.val < k.val
    · have hEq := congrArg
        (fun z : Hand (n + 1) ↦ z ⟨x.val, by omega⟩) hcd
      grind
    · have hEq := congrArg
        (fun z : Hand (n + 1) ↦ z ⟨x.val + 3, by omega⟩) hcd
      grind
  exact ⟨hvalid, hsize, removeSeqAt d k, j', hd', htarget⟩

theorem IsFullWait.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : IsFullWait (c.insertSeqAt k)) : IsFullWait c := by
  intro i
  let j : Fin (3 * (n + 1)) :=
    ⟨if i.val < k.val then i.val else i.val + 3, by split <;> omega⟩
  have hcomm : (c + single i).insertSeqAt k =
      c.insertSeqAt k + single j := by
    ext x
    grind
  exact Winning.of_insertSeqAt k (hcomm.symm ▸ hc j)

lemma insertSeqAt_standardFullWait (hn : 0 < n)
    (k : Fin (3 * n + 1)) (hk₀ : 0 < k.val) (hk₁ : k.val < 3 * n) :
    (standardFullWait n).insertSeqAt k = standardFullWait (n + 1) := by
  ext i
  grind

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
  have hpositive (i : Fin (3 * n + 1)) : 0 < c (idx i) := by
    apply interior_positive (n := n + 1) (by omega) c hc
    grind
  have hsum_le :
      (∑ i : Fin (3 * n + 1), c (idx i)) ≤ size c := by
    change (∑ i : Fin (3 * n + 1), c (idx i)) ≤
      ∑ j : Fin (3 * (n + 1)), c j
    refine sum_comp_le_sum_of_injective idx ?_ (fun j ↦ c j)
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    grind
  have hdecomp :
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i) - 1) =
        ∑ i : Fin (3 * n + 1), c (idx i) := by
    calc
      (3 * n + 1) + ∑ i : Fin (3 * n + 1), (c (idx i) - 1) =
          ∑ i : Fin (3 * n + 1), (1 + (c (idx i) - 1)) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin (3 * n + 1), c (idx i) := by
        apply Finset.sum_congr rfl
        grind
  have hexcess :
      (∑ i : Fin (3 * n + 1), (c (idx i) - 1)) ≤ 6 := by
    grind [IsFullWait.size]
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
        _ ≤ ∑ b : Fin 3, (c (idx (block a b)) - 1) :=
          Finset.single_le_sum
            (f := fun b : Fin 3 ↦ c (idx (block a b)) - 1)
            (by grind) (Finset.mem_univ b)
    have hseven :
        7 ≤ ∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)) - 1) := by
      calc
        7 = ∑ _ : Fin 7, 1 := by simp
        _ ≤ ∑ a : Fin 7, ∑ b : Fin 3, (c (idx (block a b)) - 1) :=
          Finset.sum_le_sum fun a _ ↦ hone a
    have hblocks_le :
      (∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)) - 1)) ≤
            ∑ i : Fin (3 * n + 1), (c (idx i) - 1) := by
      let pairIdx : Fin 7 × Fin 3 → Fin (3 * n + 1) :=
        fun x ↦ block x.1 x.2
      have hinj : Function.Injective pairIdx := by
        rintro ⟨a, b⟩ ⟨a', b'⟩ hab
        have hv := congrArg Fin.val hab
        grind
      simpa only [Fintype.sum_prod_type] using
        sum_comp_le_sum_of_injective pairIdx hinj
          (fun i ↦ c (idx i) - 1)
    omega
  obtain ⟨a, ha⟩ := hblock
  let k : Fin (3 * n + 1) := ⟨3 * a.val + 1, by omega⟩
  have hk₀ : 0 < k.val := by grind
  have hk₁ : k.val < 3 * n := by grind
  have hc (b : Fin 3) : c (idx (block a b)) = 1 := by
    have hv := ha b
    have hp := hpositive (block a b)
    grind
  have hc₀ : c ⟨k.val, by omega⟩ = 1 := by simpa [k, idx, block] using hc 0
  have hc₁ : c ⟨k.val + 1, by omega⟩ = 1 := by
    simpa [k, idx, block] using hc 1
  have hc₂ : c ⟨k.val + 2, by omega⟩ = 1 := by
    simpa [k, idx, block, add_assoc] using hc (2 : Fin 3)
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
                _ = (standardFullWait m).insertSeqAt k :=
                  congrArg (fun e : Hand m ↦ e.insertSeqAt k) hd
                _ = standardFullWait (m + 1) :=
                  insertSeqAt_standardFullWait (by omega) k hk₀ hk₁
            exact ih m (by omega) (by omega) ⟨hdFull, hdNe⟩

end Mahjong.Hand
