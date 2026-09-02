import Ninegates.Meldable.Basic

/-!
# Splitting a meldable hand by a zero

## Main definitions

- `filter` keeps selected coordinates of a hand and zeros the rest.
- `restrictLT` and `restrictGT` retain the hand before or after a chosen coordinate.
- `Meldable.Placement.filter`, `Meldable.Placement.restrictLT`, and
  `Meldable.Placement.restrictGT` is the placement-side analogues of the above.

## Main results

- The single and pair restriction lemmas show how elementary additions behave
  on either side of the cut.
- `Meldable.IsWitness.split_at_zero` splits a witness at a zero coordinate.
- `Meldable.split_at_zero` lifts the witness split to meldability.

## Automation

- The `filter_apply`, `restrictLT_apply`, and `restrictGT_apply` lemmas
  follow our general automation policy of apply lemmas containing `if`.
-/

namespace Mahjong.Hand

variable {n : ℕ}

def filter (keep : Fin (3 * n) → Prop) [DecidablePred keep] : Hand n →+ Hand n where
  toFun c := ⟨fun i ↦ if keep i then c i else 0⟩
  map_zero' := by apply Hand.ext; intro i; change (if keep i then 0 else 0) = 0; simp
  map_add' _ _ := by
    ext i
    change (if keep i then _ + _ else 0) =
      (if keep i then _ else 0) + (if keep i then _ else 0)
    split <;> rfl

@[grind =]
lemma filter_apply (keep : Fin (3 * n) → Prop) [DecidablePred keep]
    (c : Hand n) (i : Fin (3 * n)) :
    filter keep c i = if keep i then c i else 0 := rfl

def restrictLT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  filter (fun i ↦ i.val < k.val)

def restrictGT (k : Fin (3 * n)) : Hand n →+ Hand n :=
  filter (fun i ↦ k.val < i.val)

@[grind =]
lemma restrictLT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictLT k c i = if i.val < k.val then c i else 0 := rfl

@[grind =]
lemma restrictGT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictGT k c i = if k.val < i.val then c i else 0 := rfl

namespace Meldable.Placement

def filter
    (tripKeep seqKeep : Fin (3 * n) → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep] : Placement n →+ Placement n where
  toFun p :=
    ⟨fun i ↦ if tripKeep i then p.tripNum i else 0,
      fun i ↦ if seqKeep i then p.seqNum i else 0,
      by grind⟩
  map_zero' := by ext i <;> grind
  map_add' _ _ := by ext i <;> grind

@[grind =]
lemma tripNum_filter (tripKeep seqKeep : Fin (3 * n) → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : Fin (3 * n)) :
    (filter tripKeep seqKeep p).tripNum i =
      if tripKeep i then p.tripNum i else 0 := rfl

@[grind =]
lemma seqNum_filter (tripKeep seqKeep : Fin (3 * n) → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : Fin (3 * n)) :
    (filter tripKeep seqKeep p).seqNum i =
      if seqKeep i then p.seqNum i else 0 := rfl

def restrictLT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (fun i ↦ i.val < k.val) (fun i ↦ i.val + 2 < k.val)

def restrictGT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (fun i ↦ k.val < i.val) (fun i ↦ k.val < i.val)

@[grind =]
lemma tripNum_restrictLT_apply (k i : Fin (3 * n)) (p : Placement n) :
    (restrictLT k p).tripNum i = if i.val < k.val then p.tripNum i else 0 := rfl

@[grind =]
lemma seqNum_restrictLT_apply (k i : Fin (3 * n)) (p : Placement n) :
    (restrictLT k p).seqNum i = if i.val + 2 < k.val then p.seqNum i else 0 := rfl

@[grind =]
lemma tripNum_restrictGT_apply (k i : Fin (3 * n)) (p : Placement n) :
    (restrictGT k p).tripNum i = if k.val < i.val then p.tripNum i else 0 := rfl

@[grind =]
lemma seqNum_restrictGT_apply (k i : Fin (3 * n)) (p : Placement n) :
    (restrictGT k p).seqNum i = if k.val < i.val then p.seqNum i else 0 := rfl

end Meldable.Placement

@[simp, grind =]
lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i.val < k.val) :
    restrictLT k (single i) = single i := by grind

@[simp, grind =]
lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i.val < k.val) :
    restrictLT k (single i) = 0 := by grind

@[simp, grind =]
lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k.val < i.val) :
    restrictGT k (single i) = single i := by grind

@[simp, grind =]
lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k.val < i.val) :
    restrictGT k (single i) = 0 := by grind

@[simp, grind =]
lemma restrictLT_pair_of_lt (k i : Fin (3 * n)) (hi : i.val < k.val) :
    restrictLT k (pair i) = pair i := by grind

@[simp, grind =]
lemma restrictLT_pair_of_not_lt (k i : Fin (3 * n)) (hi : ¬i.val < k.val) :
    restrictLT k (pair i) = 0 := by grind

@[simp, grind =]
lemma restrictGT_pair_of_gt (k i : Fin (3 * n)) (hi : k.val < i.val) :
    restrictGT k (pair i) = pair i := by grind

@[simp, grind =]
lemma restrictGT_pair_of_not_gt (k i : Fin (3 * n)) (hi : ¬k.val < i.val) :
    restrictGT k (pair i) = 0 := by grind

theorem Meldable.IsWitness.split_at_zero {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : Fin (3 * n)) (hk : c k = 0) :
    IsWitness (Meldable.Placement.restrictLT k p) (restrictLT k c) ∧
      IsWitness (Meldable.Placement.restrictGT k p) (restrictGT k c) := by
  have hcross (j : Fin (3 * n)) :
      j.val ≤ k.val → k.val ≤ j.val + 2 → p.seqNum j = 0 := by grind
  grind (splits := 12)

theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : Fin (3 * n)) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  obtain ⟨p, hp⟩ := hc
  have ⟨hLT, hGT⟩ := hp.split_at_zero k hk
  exact ⟨⟨p.restrictLT k, hLT⟩, ⟨p.restrictGT k, hGT⟩⟩

end Mahjong.Hand
