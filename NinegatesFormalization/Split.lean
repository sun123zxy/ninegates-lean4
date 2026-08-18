import NinegatesFormalization.Meldable.Basic

namespace Mahjong.Hand

variable {n : ℕ}

private def filterFn {m : ℕ} (keep : ℤ → Prop) [DecidablePred keep] :
    (Fin m → ℕ) →+ (Fin m → ℕ) where
  toFun f i := if keep i.val then f i else 0
  map_zero' := by ext i; simp
  map_add' _ _ := by ext i; split <;> simp_all

def filter (keep : ℤ → Prop) [DecidablePred keep] : Hand n →+ Hand n where
  toFun c := Hand.ofFn (filterFn keep fun i ↦ c i.val)
  map_zero' := by
    ext i
    simp [filterFn, Hand.ofFn_apply]
  map_add' _ _ := by
    ext i
    simp [filterFn]
    all_goals grind

@[grind =]
lemma filter_apply (keep : ℤ → Prop) [DecidablePred keep]
    (c : Hand n) (i : ℤ) :
    filter keep c i = if keep i then c i else 0 := by
  simp [filter, filterFn, Hand.ofFn_apply]
  all_goals grind

def restrictLT (k : ℤ) : Hand n →+ Hand n := filter (· < k)

def restrictGT (k : ℤ) : Hand n →+ Hand n := filter (k < ·)

@[grind =]
lemma restrictLT_apply (k : ℤ) (c : Hand n) (i : ℤ) :
    restrictLT k c i = if i < k then c i else 0 := by
  grind [restrictLT]

@[grind =]
lemma restrictGT_apply (k : ℤ) (c : Hand n) (i : ℤ) :
    restrictGT k c i = if k < i then c i else 0 := by
  grind [restrictGT]

namespace Meldable.Placement

def filter
    (tripKeep seqKeep : ℤ → Prop) [DecidablePred tripKeep] [DecidablePred seqKeep] :
    Placement n →+ Placement n where
  toFun p := Placement.ofFn
    (filterFn tripKeep fun i ↦ p.tripNum i.val)
    (filterFn seqKeep fun i ↦ p.seqNum i.val)
  map_zero' := by congr 1 <;> funext i <;> simp [filterFn]
  map_add' _ _ := by
    congr 1 <;> funext i <;> simp [filterFn, Placement.ofFn] <;> split <;> simp_all

@[grind =]
lemma tripNum_filter (tripKeep seqKeep : ℤ → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : ℤ) :
    (filter tripKeep seqKeep p).tripNum i =
      if tripKeep i then p.tripNum i else 0 := by
  simp [filter, filterFn, Placement.tripNum_ofFn]
  all_goals grind

@[grind =]
lemma seqNum_filter (tripKeep seqKeep : ℤ → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : ℤ) :
    (filter tripKeep seqKeep p).seqNum i =
      if seqKeep i then p.seqNum i else 0 := by
  simp [filter, filterFn, Placement.seqNum_ofFn]
  all_goals grind

def restrictLT (k : ℤ) : Placement n →+ Placement n :=
  filter (· < k) (fun i ↦ i + 2 < k)

def restrictGT (k : ℤ) : Placement n →+ Placement n :=
  filter (k < ·) (k < ·)

@[grind =]
lemma tripNum_restrictLT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictLT k p).tripNum i = if i < k then p.tripNum i else 0 := by
  grind [restrictLT]

@[grind =]
lemma seqNum_restrictLT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictLT k p).seqNum i = if i + 2 < k then p.seqNum i else 0 := by
  grind [restrictLT]

@[grind =]
lemma tripNum_restrictGT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictGT k p).tripNum i = if k < i then p.tripNum i else 0 := by
  grind [restrictGT]

@[grind =]
lemma seqNum_restrictGT (k : ℤ) (p : Placement n) (i : ℤ) :
    (restrictGT k p).seqNum i = if k < i then p.seqNum i else 0 := by
  grind [restrictGT]

end Meldable.Placement

@[simp, grind =]
lemma restrictLT_single_of_lt (k : ℤ) (i : Fin (3 * n)) (hi : i.val < k) :
    restrictLT k (single i) = single i := by ext j; grind

@[simp, grind =]
lemma restrictLT_single_of_not_lt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬(i.val : ℤ) < k) :
    restrictLT k (single i) = 0 := by ext j; grind

@[simp, grind =]
lemma restrictGT_single_of_gt (k : ℤ) (i : Fin (3 * n)) (hi : k < i.val) :
    restrictGT k (single i) = single i := by ext j; grind

@[simp, grind =]
lemma restrictGT_single_of_not_gt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬k < (i.val : ℤ)) :
    restrictGT k (single i) = 0 := by ext j; grind

@[simp, grind =]
lemma restrictLT_pair_of_lt (k : ℤ) (i : Fin (3 * n)) (hi : i.val < k) :
    restrictLT k (pair i) = pair i := by simp [pair, hi]

@[simp, grind =]
lemma restrictLT_pair_of_not_lt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬(i.val : ℤ) < k) :
    restrictLT k (pair i) = 0 := by simp [pair, hi]

@[simp, grind =]
lemma restrictGT_pair_of_gt (k : ℤ) (i : Fin (3 * n)) (hi : k < i.val) :
    restrictGT k (pair i) = pair i := by simp [pair, hi]

@[simp, grind =]
lemma restrictGT_pair_of_not_gt
    (k : ℤ) (i : Fin (3 * n)) (hi : ¬k < (i.val : ℤ)) :
    restrictGT k (pair i) = 0 := by simp [pair, hi]

theorem Meldable.IsWitness.split_at_zero {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : ℤ) (hk : c k = 0) :
    IsWitness (Meldable.Placement.restrictLT k p) (restrictLT k c) ∧
      IsWitness (Meldable.Placement.restrictGT k p) (restrictGT k c) := by
  grind only [IsWitness, Placement.toHand_apply, restrictLT_apply, Placement.tripNum_restrictLT,
    Placement.seqNum_restrictLT, restrictGT_apply, Placement.tripNum_restrictGT,
    Placement.seqNum_restrictGT]

theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : ℤ) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  obtain ⟨p, hp⟩ := hc
  have ⟨hLT, hGT⟩ := hp.split_at_zero k hk
  exact ⟨⟨p.restrictLT k, hLT⟩, ⟨p.restrictGT k, hGT⟩⟩

end Mahjong.Hand
