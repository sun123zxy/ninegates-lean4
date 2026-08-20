import NinegatesFormalization.Meldable.Basic

namespace Mahjong.Hand

variable {n : ℕ}

def filter (keep : Fin (3 * n) → Prop) [DecidablePred keep] : Hand n →+ Hand n where
  toFun c := ⟨fun i ↦ if keep i then c i else 0⟩
  map_zero' := by apply Hand.ext; intro i; change (if keep i then 0 else 0) = 0; simp
  map_add' _ _ := by
    apply Hand.ext
    intro i
    change (if keep i then _ + _ else 0) =
      (if keep i then _ else 0) + (if keep i then _ else 0)
    split <;> rfl

@[simp, grind =]
lemma filter_apply (keep : Fin (3 * n) → Prop) [DecidablePred keep]
    (c : Hand n) (i : Fin (3 * n)) :
    filter keep c i = if keep i then c i else 0 := rfl

def restrictLT (k : Fin (3 * n)) : Hand n →+ Hand n := filter (· < k)

def restrictGT (k : Fin (3 * n)) : Hand n →+ Hand n := filter (k < ·)

@[simp, grind =]
lemma restrictLT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictLT k c i = if i < k then c i else 0 := rfl

@[simp, grind =]
lemma restrictGT_apply (k i : Fin (3 * n)) (c : Hand n) :
    restrictGT k c i = if k < i then c i else 0 := rfl

namespace Meldable.Placement

def filter
    (tripKeep seqKeep : Fin (3 * n) → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep] : Placement n →+ Placement n where
  toFun p :=
    ⟨fun i ↦ if tripKeep i then p.tripNum i else 0,
      fun i ↦ if seqKeep i then p.seqNum i else 0, by
        constructor
        · intro i hi
          simp [p.seqNum_tail.1 i hi]
        · intro i hi
          simp [p.seqNum_tail.2 i hi]⟩
  map_zero' := by ext i <;> simp
  map_add' _ _ := by ext i <;> simp [add_apply, add_assoc] <;> split <;> simp

@[simp, grind =]
lemma tripNum_filter (tripKeep seqKeep : Fin (3 * n) → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : Fin (3 * n)) :
    (filter tripKeep seqKeep p).tripNum i =
      if tripKeep i then p.tripNum i else 0 := rfl

@[simp, grind =]
lemma seqNum_filter (tripKeep seqKeep : Fin (3 * n) → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : Fin (3 * n)) :
    (filter tripKeep seqKeep p).seqNum i =
      if seqKeep i then p.seqNum i else 0 := rfl

def restrictLT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (· < k) (fun i ↦ i.val + 2 < k.val)

def restrictGT (k : Fin (3 * n)) : Placement n →+ Placement n :=
  filter (k < ·) (k < ·)

@[simp, grind =]
lemma tripNum_restrictLT (k i : Fin (3 * n)) (p : Placement n) :
    (restrictLT k p).tripNum i = if i < k then p.tripNum i else 0 := rfl

@[simp, grind =]
lemma seqNum_restrictLT (k i : Fin (3 * n)) (p : Placement n) :
    (restrictLT k p).seqNum i = if i.val + 2 < k.val then p.seqNum i else 0 := rfl

@[simp, grind =]
lemma tripNum_restrictGT (k i : Fin (3 * n)) (p : Placement n) :
    (restrictGT k p).tripNum i = if k < i then p.tripNum i else 0 := rfl

@[simp, grind =]
lemma seqNum_restrictGT (k i : Fin (3 * n)) (p : Placement n) :
    (restrictGT k p).seqNum i = if k < i then p.seqNum i else 0 := rfl

end Meldable.Placement

@[simp, grind =]
lemma restrictLT_single_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (single i) = single i := by apply DFunLike.ext; grind [restrictLT]

@[simp, grind =]
lemma restrictLT_single_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (single i) = 0 := by apply DFunLike.ext; grind [restrictLT]

@[simp, grind =]
lemma restrictGT_single_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (single i) = single i := by apply DFunLike.ext; grind [restrictGT]

@[simp, grind =]
lemma restrictGT_single_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (single i) = 0 := by apply DFunLike.ext; grind [restrictGT]

@[simp, grind =]
lemma restrictLT_pair_of_lt (k i : Fin (3 * n)) (hi : i < k) :
    restrictLT k (pair i) = pair i := by simp [pair, hi]

@[simp, grind =]
lemma restrictLT_pair_of_not_lt (k i : Fin (3 * n)) (hi : ¬i < k) :
    restrictLT k (pair i) = 0 := by simp [pair, hi]

@[simp, grind =]
lemma restrictGT_pair_of_gt (k i : Fin (3 * n)) (hi : k < i) :
    restrictGT k (pair i) = pair i := by simp [pair, hi]

@[simp, grind =]
lemma restrictGT_pair_of_not_gt (k i : Fin (3 * n)) (hi : ¬k < i) :
    restrictGT k (pair i) = 0 := by simp [pair, hi]

theorem Meldable.IsWitness.split_at_zero {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : Fin (3 * n)) (hk : c k = 0) :
    IsWitness (Meldable.Placement.restrictLT k p) (restrictLT k c) ∧
      IsWitness (Meldable.Placement.restrictGT k p) (restrictGT k c) := by
  constructor <;> unfold IsWitness
  · ext i
    grind only [IsWitness, Meldable.Placement.toHand_apply, restrictLT_apply,
      Meldable.Placement.tripNum_restrictLT,
      Meldable.Placement.seqNum_restrictLT]
  · ext i
    grind only [IsWitness, Meldable.Placement.toHand_apply, restrictGT_apply,
      Meldable.Placement.tripNum_restrictGT,
      Meldable.Placement.seqNum_restrictGT]

theorem Meldable.split_at_zero {c : Hand n} (hc : Meldable c)
    (k : Fin (3 * n)) (hk : c k = 0) :
    Meldable (restrictLT k c) ∧ Meldable (restrictGT k c) := by
  obtain ⟨p, hp⟩ := hc
  have ⟨hLT, hGT⟩ := hp.split_at_zero k hk
  exact ⟨⟨p.restrictLT k, hLT⟩, ⟨p.restrictGT k, hGT⟩⟩

end Mahjong.Hand
