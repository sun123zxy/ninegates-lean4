import NinegatesFormalization.Positivity
import NinegatesFormalization.Standard

/-!
# Full-wait reduction

## Main definitions

- `insertSeqAt` inserts one complete sequence (`{1,1,1}`) at an interior coordinate.
- `insertSeqEquiv` identifies the old coordinates and the inserted sequence
  with the coordinates of the enlarged hand.
- `removeSeqAt` is the inverse operation used by the reduction step.
- `IsCounterexample` is a transparent predicate for a full wait that is not the standard full wait.

## Main results

- `Meldable.of_insertSeqAt` shows that deleting a sequence preserves meldability.
- `Winning.of_insertSeqAt` shows that deleting a sequence preserves winning property.
- `IsCounterexample.of_insertSeqAt` shows that deleting an interior sequence preserves
  counterexamples.
- `exists_insertSeqAt_of_large` finds a removable sequence in every sufficiently large full wait.
- `full_wait_reduction` shows that a larger counterexample yields a smaller
  counterexample in the small cases, using `exists_insertSeqAt_of_large`.

## Design notes

- The automation design of `insertSeqAt_apply` and `removeSeqAt_apply` follow
  our general automation policy of apply lemmas containing `if`.
-/

namespace Mahjong.Hand

variable {n : ℕ}

def insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) : Hand (n + 1) :=
  ⟨fun i ↦ if h : i.val < k.val then c ⟨i.val, by omega⟩
           else if h : i.val < k.val + 3 then 1
           else c ⟨i.val - 3, by omega⟩⟩

@[grind =]
lemma insertSeqAt_apply (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) : c.insertSeqAt k i =
    if h : i.val < k.val then c ⟨i.val, by omega⟩
    else if h : i.val < k.val + 3 then 1
    else c ⟨i.val - 3, by omega⟩ := rfl

@[simp]
lemma insertSeqAt_apply_of_lt (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) (hi : i.val < k.val) :
    c.insertSeqAt k i = c ⟨i.val, by omega⟩ := by grind

@[simp]
lemma insertSeqAt_apply_of_mem (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) (hi₀ : k.val ≤ i.val) (hi₁ : i.val < k.val + 3) :
    c.insertSeqAt k i = 1 := by grind

@[simp]
lemma insertSeqAt_apply_of_ge (c : Hand n) (k : Fin (3 * n + 1))
    (i : Fin (3 * (n + 1))) (hi : k.val + 3 ≤ i.val) :
    c.insertSeqAt k i = c ⟨i.val - 3, by omega⟩ := by grind

def insertSeqEquiv (k : Fin (3 * n + 1)) :
    Fin (3 * n) ⊕ Fin 3 ≃ Fin (3 * (n + 1)) where
  toFun x := match x with
    | .inl i => ⟨if i.val < k.val then i.val else i.val + 3, by grind⟩
    | .inr j => ⟨k.val + j.val, by omega⟩
  invFun i :=
    if h₀ : i.val < k.val then .inl ⟨i.val, by omega⟩
    else if h₁ : i.val < k.val + 3 then .inr ⟨i.val - k.val, by omega⟩
    else .inl ⟨i.val - 3, by omega⟩
  left_inv x := by grind
  right_inv i := by
    apply Fin.ext
    by_cases hi₀ : i.val < k.val
    · simp [hi₀]
    · by_cases hi₁ : i.val < k.val + 3
      · simp [hi₀, hi₁]
        omega
      · have hi₂ : ¬i.val - 3 < k.val := by omega
        simp [hi₀, hi₁, hi₂]
        omega

@[simp, grind =]
lemma insertSeqEquiv_inl_val (k : Fin (3 * n + 1)) (i : Fin (3 * n)) :
    (insertSeqEquiv k (.inl i)).val = if i.val < k.val then i.val else i.val + 3 :=
  rfl

@[simp, grind =]
lemma insertSeqEquiv_inr_val (k : Fin (3 * n + 1)) (i : Fin 3) :
    (insertSeqEquiv k (.inr i)).val = k.val + i.val := rfl

@[grind =]
lemma size_insertSeqAt (c : Hand n) (k : Fin (3 * n + 1)) :
    size (c.insertSeqAt k) = size c + 3 := by
  have hinl (i : Fin (3 * n)) : c.insertSeqAt k (insertSeqEquiv k (.inl i)) = c i := by grind
  have hinr (i : Fin 3) : c.insertSeqAt k (insertSeqEquiv k (.inr i)) = 1 := by grind
  change (∑ i : Fin (3 * (n + 1)), c.insertSeqAt k i) =
    (∑ i : Fin (3 * n), c i) + 3
  calc
    _ = ∑ x : Fin (3 * n) ⊕ Fin 3, c.insertSeqAt k (insertSeqEquiv k x) :=
      (Equiv.sum_comp (insertSeqEquiv k) (fun i ↦ c.insertSeqAt k i)).symm
    _ = _ := by simp [Fintype.sum_sum_type, hinl, hinr]

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

@[simp]
lemma removeSeqAt_apply_of_lt (c : Hand (n + 1)) (k : Fin (3 * n + 1))
    (i : Fin (3 * n)) (hi : i.val < k.val) :
    removeSeqAt c k i = c ⟨i.val, by omega⟩ := by grind

@[simp]
lemma removeSeqAt_apply_of_ge (c : Hand (n + 1)) (k : Fin (3 * n + 1))
    (i : Fin (3 * n)) (hi : k.val ≤ i.val) :
    removeSeqAt c k i = c ⟨i.val + 3, by omega⟩ := by grind

@[simp, grind =]
lemma insertSeqAt_removeSeqAt (c : Hand (n + 1))
    (k : Fin (3 * n + 1)) (h₀ : c ⟨k.val, by omega⟩ = 1)
    (h₁ : c ⟨k.val + 1, by omega⟩ = 1) (h₂ : c ⟨k.val + 2, by omega⟩ = 1) :
    (removeSeqAt c k).insertSeqAt k = c := by
  ext i; grind

/- Note that this is a standalone proof. It does not rely on the scan algorithm. -/
theorem Meldable.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Meldable (c.insertSeqAt k)) : Meldable c := by
  rcases hc with ⟨p, hp⟩
  unfold Meldable.IsWitness at hp
  let k₀ : Fin (3 * (n + 1)) := ⟨k.val, by omega⟩
  let k₁ : Fin (3 * (n + 1)) := ⟨k.val + 1, by omega⟩
  let k₂ : Fin (3 * (n + 1)) := ⟨k.val + 2, by omega⟩
  have hp_at (i : Fin (3 * (n + 1))) := congrArg (fun d : Hand (n + 1) ↦ d i) hp
  have h₀ := hp_at k₀
  have h₁ := hp_at k₁
  have h₂ := hp_at k₂
  have hseq₁ (hk : 2 ≤ k.val) : p.seqNum k₁ = p.seqNum ⟨k.val - 2, by omega⟩ := by grind
  have hseq₂ (hk : 1 ≤ k.val) : p.seqNum k₂ = p.seqNum ⟨k.val - 1, by omega⟩ := by grind
  let seqNum (i : Fin (3 * n)) :=
    if _h : i.val < k.val then p.seqNum ⟨i.val, by omega⟩
    else p.seqNum ⟨i.val + 3, by omega⟩
  have htail (i : Fin (3 * n)) (hi : 3 * n - 2 ≤ i.val) : seqNum i = 0 := by grind
  let q : Meldable.Placement n :=
    ⟨(fun i ↦ if h : i.val < k.val then p.tripNum ⟨i.val, by omega⟩
              else p.tripNum ⟨i.val + 3, by omega⟩),
     seqNum,
     by constructor <;> intro i hi <;> apply htail i <;> omega⟩
  use q; unfold Meldable.IsWitness; ext i
  simp only [q, Meldable.Placement.toHand_apply]
  have hpi := hp_at (insertSeqEquiv k (.inl i))
  simp only [Meldable.Placement.toHand_apply, insertSeqAt_apply, insertSeqEquiv_inl_val] at hpi
  by_cases hi : i.val < k.val
  · grind
  by_cases hi' : k.val + 2 ≤ i.val
  · grind
  have hicases : i.val = k.val ∨ i.val = k.val + 1 := by omega
  rcases hicases with hik | hik <;> grind

theorem Winning.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : Winning (c.insertSeqAt k)) : Winning c := by
  rcases hc with ⟨hcvalid, hcsize, d, j, hd, hcd⟩
  have hvalid : Valid c := by
    intro i
    have h := hcvalid (insertSeqEquiv k (.inl i))
    grind
  use hvalid, by grind, removeSeqAt d k
  have hj : j.val < k.val ∨ k.val + 3 ≤ j.val := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z j) hcd
    grind
  have hd_at (i : Fin 3) : d ⟨k.val + i.val, by omega⟩ = 1 := by
    have hEq := congrArg (fun z : Hand (n + 1) ↦ z (insertSeqEquiv k (.inr i))) hcd
    grind
  have hdEq : (removeSeqAt d k).insertSeqAt k = d :=
    insertSeqAt_removeSeqAt d k (by simpa using hd_at 0)
      (by simpa using hd_at 1) (by simpa using hd_at 2)
  let j' : Fin (3 * n) := ⟨if j.val < k.val then j.val else j.val - 3, by split <;> omega⟩
  have hd' : Meldable (removeSeqAt d k) := by
    apply Meldable.of_insertSeqAt k
    simpa only [hdEq] using hd
  use j', hd'
  ext x
  have hEq := congrArg (fun z : Hand (n + 1) ↦ z (insertSeqEquiv k (.inl x))) hcd
  grind

theorem IsFullWait.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hc : IsFullWait (c.insertSeqAt k)) : IsFullWait c := by
  intro i
  let j : Fin (3 * (n + 1)) :=
    ⟨if i.val < k.val then i.val else i.val + 3, by split <;> omega⟩
  have hcomm : (c + single i).insertSeqAt k = c.insertSeqAt k + single j := by
    ext x; grind
  exact Winning.of_insertSeqAt k (hcomm.symm ▸ hc j)

lemma insertSeqAt_standardFullWait (hn : 0 < n)
    (k : Fin (3 * n + 1)) (hk₀ : 0 < k.val) (hk₁ : k.val < 3 * n) :
    (standardFullWait n).insertSeqAt k = standardFullWait (n + 1) := by
  ext i; grind

private lemma sum_comp_le_sum_of_injective {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (g : β → ℕ) : ∑ i, g (f i) ≤ ∑ j, g j := by
  classical
  calc
    ∑ i, g (f i) = ∑ j ∈ Finset.univ.image f, g j :=
      (Finset.sum_image hf.injOn).symm
    _ ≤ ∑ j, g j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem exists_insertSeqAt_of_large (hn : 6 < n) {c : Hand (n + 1)} (hc : IsFullWait c) :
    ∃ d : Hand n, ∃ k : Fin (3 * n + 1), 0 < k.val ∧ k.val < 3 * n ∧ c = d.insertSeqAt k := by
  let idx : Fin (3 * (n + 1) - 2) → Fin (3 * (n + 1)) :=
    fun i ↦ ⟨i.val + 1, by omega⟩
  have hpositive (i : Fin (3 * (n + 1) - 2)) : 0 < c (idx i) := by
    apply interior_positive (n := n + 1) (by omega) c hc
    grind
  have hexcess : (∑ i : Fin (3 * (n + 1) - 2), (c (idx i) - 1)) ≤ 6 := by
    simpa [idx] using (interior_excess_le_six (n := n + 1) (c := c) (by omega) hc)
  let block : Fin 7 → Fin 3 → Fin (3 * (n + 1) - 2) :=
    fun a b ↦ ⟨3 * a.val + b.val, by omega⟩
  have hblock : ∃ a : Fin 7, ∀ b : Fin 3, c (idx (block a b)) - 1 = 0 := by
    by_contra h
    push Not at h
    have hone (a : Fin 7) : 1 ≤ ∑ b : Fin 3, (c (idx (block a b)) - 1) := by
      obtain ⟨b, hb⟩ := h a
      calc
        1 ≤ c (idx (block a b)) - 1 := Nat.one_le_iff_ne_zero.mpr hb
        _ ≤ ∑ b : Fin 3, (c (idx (block a b)) - 1) :=
          Finset.single_le_sum
            (f := fun b : Fin 3 ↦ c (idx (block a b)) - 1)
            (by grind) (Finset.mem_univ b)
    have hseven : 7 ≤ ∑ a : Fin 7, ∑ b : Fin 3, (c (idx (block a b)) - 1) := by
      calc
        7 = ∑ _ : Fin 7, 1 := by simp
        _ ≤ ∑ a : Fin 7, ∑ b : Fin 3, (c (idx (block a b)) - 1) :=
          Finset.sum_le_sum fun a _ ↦ hone a
    have hblocks_le :
      (∑ a : Fin 7, ∑ b : Fin 3,
          (c (idx (block a b)) - 1)) ≤
            ∑ i : Fin (3 * (n + 1) - 2), (c (idx i) - 1) := by
      let pairIdx : Fin 7 × Fin 3 → Fin (3 * (n + 1) - 2) :=
        fun x ↦ block x.1 x.2
      have hinj : Function.Injective pairIdx := by
        grind [Function.Injective]
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

lemma IsCounterexample.of_insertSeqAt {c : Hand n} (k : Fin (3 * n + 1))
    (hk₀ : 0 < k.val) (hk₁ : k.val < 3 * n)
    (hc : IsCounterexample (c.insertSeqAt k)) : IsCounterexample c := by
  constructor
  · exact IsFullWait.of_insertSeqAt k hc.1
  · intro hstandard
    apply hc.2
    calc
      c.insertSeqAt k = (standardFullWait n).insertSeqAt k :=
        congrArg (fun d : Hand n ↦ d.insertSeqAt k) hstandard
      _ = standardFullWait (n + 1) :=
        insertSeqAt_standardFullWait (by omega) k hk₀ hk₁

theorem full_wait_reduction {n : ℕ} (hn : 2 ≤ n) {c : Hand n} (hc : IsCounterexample c) :
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
            have hd := IsCounterexample.of_insertSeqAt k hk₀ hk₁ (hcd ▸ hc)
            exact ih m (by omega) (by omega) hd

end Mahjong.Hand
