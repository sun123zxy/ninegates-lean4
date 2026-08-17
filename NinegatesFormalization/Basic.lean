import Mathlib

namespace Mahjong

private def extend {m : ℕ} (f : Fin m → ℕ) (i : ℤ) : ℕ :=
  if h : 0 ≤ i ∧ i < m then f ⟨i.toNat, by omega⟩ else 0

@[simp]
private lemma extend_coe {m : ℕ} (f : Fin m → ℕ) (i : Fin m) :
    extend f i.val = f i := by
  grind [extend]

private lemma extend_of_lt_zero {m : ℕ} (f : Fin m → ℕ) (i : ℤ) (hi : i < 0) :
    extend f i = 0 := by simp [extend, hi]

private lemma extend_of_ge {m : ℕ} (f : Fin m → ℕ) (i : ℤ) (hi : m ≤ i) :
    extend f i = 0 := by simp [extend, show ¬(0 ≤ i ∧ i < m) by omega]

@[simp]
private lemma extend_zero {m : ℕ} (i : ℤ) :
    extend (0 : Fin m → ℕ) i = 0 := by simp [extend]

private lemma extend_add {m : ℕ} (f g : Fin m → ℕ) (i : ℤ) :
    extend (f + g) i = extend f i + extend g i := by
  by_cases h : 0 ≤ i ∧ i < m <;> simp [extend, h]

private lemma extend_nsmul {m : ℕ} (k : ℕ) (f : Fin m → ℕ) (i : ℤ) :
    extend (k • f) i = k * extend f i := by
  by_cases h : 0 ≤ i ∧ i < m <;> simp [extend, h]

private lemma extend_filter {m : ℕ} (f : Fin m → ℕ)
    (keep : ℤ → Prop) [DecidablePred keep] (i : ℤ) :
    extend (fun j ↦ if keep j.val then f j else 0) i =
      if keep i then extend f i else 0 := by
  grind [extend]

@[simp]
private lemma extend_single {m : ℕ} (a : ℕ) (i : Fin m) (j : ℤ) :
    extend (fun k ↦ if k = i then a else 0) j =
      if j = i.val then a else 0 := by
  grind [extend]

structure Hand (n : ℕ) where
  private mk ::
  private count : Fin (3 * n) → ℕ

namespace Hand

variable {n : ℕ}

def ofFn (f : Fin (3 * n) → ℕ) : Hand n := .mk f

instance : FunLike (Hand n) ℤ ℕ where
  coe c := extend c.count
  coe_injective := by
    intro c d h
    cases c
    cases d
    congr
    funext i
    simpa using congrFun h i.val

@[simp, grind =]
lemma ofFn_apply (f : Fin (3 * n) → ℕ) (i : Fin (3 * n)) :
    ofFn f i.val = f i :=
  extend_coe _ _

@[simp, grind =]
lemma apply_of_lt_zero (c : Hand n) (i : ℤ) (hi : i < 0) : c i = 0 :=
  extend_of_lt_zero _ _ hi

@[simp, grind =]
lemma apply_of_ge (c : Hand n) (i : ℤ) (hi : 3 * n ≤ i) : c i = 0 :=
  extend_of_ge _ _ hi

@[ext, grind ext]
lemma ext {c d : Hand n} (h : ∀ i : ℤ, c i = d i) : c = d :=
  DFunLike.ext c d h

instance : Zero (Hand n) := ⟨ofFn 0⟩

instance : Add (Hand n) :=
  ⟨fun c d ↦ ofFn (c.count + d.count)⟩

instance : SMul ℕ (Hand n) :=
  ⟨fun k c ↦ ofFn (k • c.count)⟩

instance : IsZeroApply (Hand n) ℤ ℕ where
  zero_apply _ := extend_zero _

instance : IsAddApply (Hand n) ℤ ℕ where
  add_apply _ _ _ := extend_add _ _ _

instance : IsSMulApply ℕ (Hand n) ℤ ℕ where
  smul_apply _ _ _ := extend_nsmul _ _ _

instance : AddCommMonoid (Hand n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc c d e := by ext i; simp [add_assoc]
  zero_add c := by ext i; simp
  add_zero c := by ext i; simp
  add_comm c d := by ext i; simp [add_comm]
  nsmul_zero k := by ext i; simp
  nsmul_succ k c := by ext i; simp [Nat.succ_mul, add_comm]

def size : Hand n →+ ℕ where
  toFun c := ∑ i : Fin (3 * n), c i.val
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

def sum : Hand n →+ ℕ where
  toFun c := ∑ i : Fin (3 * n), i.val * c i.val
  map_zero' := by simp
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]

@[grind =]
def single (i : Fin (3 * n)) : Hand n := ofFn fun j ↦ if j = i then 1 else 0

@[simp, grind =]
lemma single_apply (i : Fin (3 * n)) (j : ℤ) :
    single i j = if j = i.val then 1 else 0 :=
  extend_single 1 i j

@[simp, grind =]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by simp [size, single]

@[simp, grind =]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by simp [sum, single]

@[grind =]
def pair (i : Fin (3 * n)) : Hand n := 2 • single i

@[simp, grind =]
lemma pair_apply (i : Fin (3 * n)) (j : ℤ) :
    pair i j = if j = i.val then 2 else 0 := by simp [pair]

@[simp, grind =]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by simp [pair]

@[simp, grind =]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by simp [pair]

@[grind =]
def triplet (i : Fin (3 * n)) : Hand n := 3 • single i

@[simp, grind =]
lemma triplet_apply (i : Fin (3 * n)) (j : ℤ) :
    triplet i j = if j = i.val then 3 else 0 := by simp [triplet]

@[simp, grind =]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by simp [triplet]

@[simp, grind =]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by simp [triplet]

@[grind =]
def sequence (i : Fin (3 * n - 2)) : Hand n :=
  single ⟨i, by omega⟩ + single ⟨i + 1, by omega⟩ + single ⟨i + 2, by omega⟩

@[simp, grind =]
lemma sequence_apply (i : Fin (3 * n - 2)) (j : ℤ) :
    sequence i j =
      if j = i.val ∨ j = i.val + 1 ∨ j = i.val + 2 then 1 else 0 := by
  simp only [sequence, add_apply, single_apply]
  split_ifs <;> omega

@[simp, grind =]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by simp [sequence]

@[simp, grind =]
lemma sum_sequence (i : Fin (3 * n - 2)) :
    sum (sequence i) = 3 * (i.val + 1) := by
  simp [sequence]
  omega

def Valid (c : Hand n) : Prop := ∀ i : Fin (3 * n), c i.val ≤ 4

namespace Meldable

structure Placement (n : ℕ) where
  private mk ::
  private tripNum' : Fin (3 * n) → ℕ
  private seqNum' : Fin (3 * n - 2) → ℕ

namespace Placement

def ofFn (tripNum : Fin (3 * n) → ℕ) (seqNum : Fin (3 * n - 2) → ℕ) :
    Placement n := .mk tripNum seqNum

private lemma ext_raw {p q : Placement n}
    (htrip : ∀ i, p.tripNum' i = q.tripNum' i)
    (hseq : ∀ i, p.seqNum' i = q.seqNum' i) : p = q := by
  cases p
  cases q
  congr <;> funext i <;> simp_all

instance : Zero (Placement n) := ⟨ofFn 0 0⟩

instance : Add (Placement n) :=
  ⟨fun p q ↦ ofFn (p.tripNum' + q.tripNum') (p.seqNum' + q.seqNum')⟩

instance : SMul ℕ (Placement n) :=
  ⟨fun k p ↦ ofFn (k • p.tripNum') (k • p.seqNum')⟩

instance : AddCommMonoid (Placement n) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc p q r := by apply ext_raw <;> intro i <;> exact add_assoc _ _ _
  zero_add p := by apply ext_raw <;> intro i <;> exact zero_add _
  add_zero p := by apply ext_raw <;> intro i <;> exact add_zero _
  add_comm p q := by apply ext_raw <;> intro i <;> exact add_comm _ _
  nsmul_zero k := by apply ext_raw <;> intro i <;> exact Nat.zero_mul _
  nsmul_succ k p := by apply ext_raw <;> intro i <;> exact Nat.succ_mul k _

def tripNum : Placement n →+ (ℤ → ℕ) where
  toFun p := extend p.tripNum'
  map_zero' := by
    funext i
    change extend (0 : Fin (3 * n) → ℕ) i = 0
    exact extend_zero i
  map_add' p q := by
    funext i
    change extend (p.tripNum' + q.tripNum') i =
      extend p.tripNum' i + extend q.tripNum' i
    exact extend_add _ _ _

def seqNum : Placement n →+ (ℤ → ℕ) where
  toFun p := extend p.seqNum'
  map_zero' := by
    funext i
    change extend (0 : Fin (3 * n - 2) → ℕ) i = 0
    exact extend_zero i
  map_add' p q := by
    funext i
    change extend (p.seqNum' + q.seqNum') i =
      extend p.seqNum' i + extend q.seqNum' i
    exact extend_add _ _ _

@[simp, grind =]
lemma tripNum_ofFn (trip : Fin (3 * n) → ℕ) (seq : Fin (3 * n - 2) → ℕ)
    (i : Fin (3 * n)) :
    (ofFn trip seq).tripNum i.val = trip i := extend_coe _ _

@[simp, grind =]
lemma seqNum_ofFn (trip : Fin (3 * n) → ℕ) (seq : Fin (3 * n - 2) → ℕ)
    (i : Fin (3 * n - 2)) :
    (ofFn trip seq).seqNum i.val = seq i := extend_coe _ _

@[simp, grind =]
lemma tripNum_of_lt_zero (p : Placement n) (i : ℤ) (hi : i < 0) :
    p.tripNum i = 0 :=
  extend_of_lt_zero _ _ hi

@[simp, grind =]
lemma tripNum_of_ge (p : Placement n) (i : ℤ) (hi : 3 * n ≤ i) :
    p.tripNum i = 0 :=
  extend_of_ge _ _ hi

@[simp, grind =]
lemma seqNum_of_lt_zero (p : Placement n) (i : ℤ) (hi : i < 0) :
    p.seqNum i = 0 :=
  extend_of_lt_zero _ _ hi

@[simp, grind =]
lemma seqNum_of_ge (p : Placement n) (i : ℤ) (hi : (3 * n - 2 : ℕ) ≤ i) :
    p.seqNum i = 0 :=
  extend_of_ge _ _ hi

private lemma ext_fin {p q : Placement n}
    (htrip : ∀ i : Fin (3 * n), p.tripNum i.val = q.tripNum i.val)
    (hseq : ∀ i : Fin (3 * n - 2), p.seqNum i.val = q.seqNum i.val) : p = q := by
  apply ext_raw
  · intro i
    simpa [tripNum] using htrip i
  · intro i
    simpa [seqNum] using hseq i

@[ext, grind ext]
lemma ext {p q : Placement n}
    (htrip : ∀ i : ℤ, p.tripNum i = q.tripNum i)
    (hseq : ∀ i : ℤ, p.seqNum i = q.seqNum i) : p = q :=
  ext_fin (fun i ↦ htrip i.val) (fun i ↦ hseq i.val)

@[grind =]
def toHand : Placement n →+ Hand n where
  toFun p := Hand.ofFn fun i ↦
    3 * p.tripNum i.val + p.seqNum i.val +
      p.seqNum ((i.val : ℤ) - 1) + p.seqNum ((i.val : ℤ) - 2)
  map_zero' := by
    change Hand.ofFn _ = Hand.ofFn _
    congr 1
    funext i
    simp
  map_add' _ _ := by
    change Hand.ofFn _ = Hand.ofFn _
    congr 1
    funext i
    simp [Hand.ofFn]
    omega

@[simp, grind =]
theorem toHand_apply (p : Placement n) (i : ℤ) :
    p.toHand i =
      3 * p.tripNum i + p.seqNum i + p.seqNum (i - 1) + p.seqNum (i - 2) := by
  by_cases hlo : i < 0
  · have h1 : i - 1 < 0 := by omega
    have h2 : i - 2 < 0 := by omega
    simp [Hand.apply_of_lt_zero _ _ hlo, tripNum_of_lt_zero _ _ hlo,
      seqNum_of_lt_zero _ _ hlo, seqNum_of_lt_zero _ _ h1,
      seqNum_of_lt_zero _ _ h2]
  by_cases hhi : 3 * n ≤ i
  · have h0 : (3 * n - 2 : ℕ) ≤ i := by omega
    have h1 : p.seqNum (i - 1) = 0 := by
      by_cases h : i - 1 < 0
      · exact seqNum_of_lt_zero _ _ h
      · apply seqNum_of_ge
        omega
    have h2 : p.seqNum (i - 2) = 0 := by
      by_cases h : i - 2 < 0
      · exact seqNum_of_lt_zero _ _ h
      · apply seqNum_of_ge
        omega
    simp [Hand.apply_of_ge _ _ hhi, tripNum_of_ge _ _ hhi,
      seqNum_of_ge _ _ h0, h1, h2]
  let k : Fin (3 * n) := ⟨i.toNat, by omega⟩
  have hk : (k.val : ℤ) = i := Int.toNat_of_nonneg (by omega)
  simpa [toHand, hk] using Hand.ofFn_apply
    (fun j : Fin (3 * n) ↦
      3 * p.tripNum j.val + p.seqNum j.val +
        p.seqNum ((j.val : ℤ) - 1) + p.seqNum ((j.val : ℤ) - 2)) k

@[grind =]
theorem toHand_eq_sum (p : Placement n) :
    p.toHand =
      ∑ i, p.tripNum i.val • Hand.triplet i +
        ∑ j, p.seqNum j.val • Hand.sequence j := by
  let tripPiece (i : Fin (3 * n)) :=
    ofFn (fun j ↦ if j = i then 1 else 0) 0
  let seqPiece (i : Fin (3 * n - 2)) :=
    ofFn 0 (fun j ↦ if j = i then 1 else 0)
  have hdecomp :
      p = ∑ i, p.tripNum i.val • tripPiece i +
        ∑ j, p.seqNum j.val • seqPiece j := by
    apply ext_fin
    · intro k
      simp [tripPiece, seqPiece]
    · intro k
      simp [tripPiece, seqPiece]
  have htrip (i : Fin (3 * n)) : (tripPiece i).toHand = Hand.triplet i := by
    apply Hand.ext
    intro k
    simp [toHand_apply, Hand.triplet_apply, tripPiece, tripNum, seqNum, ofFn]
  have hseq (i : Fin (3 * n - 2)) : (seqPiece i).toHand = Hand.sequence i := by
    apply Hand.ext
    intro k
    simp only [toHand_apply, Hand.sequence_apply]
    simp [seqPiece, tripNum, seqNum, ofFn]
    split_ifs <;> omega
  calc
    p.toHand =
        (∑ i, p.tripNum i.val • tripPiece i +
          ∑ j, p.seqNum j.val • seqPiece j).toHand := congrArg toHand hdecomp
    _ = ∑ i, p.tripNum i.val • (tripPiece i).toHand +
          ∑ j, p.seqNum j.val • (seqPiece j).toHand := by simp
    _ = _ := by simp only [htrip, hseq]

end Placement

def IsWitness (p : Meldable.Placement n) (c : Hand n) : Prop := p.toHand = c

@[grind ←]
lemma IsWitness.add {p q : Meldable.Placement n} {c d : Hand n}
    (hp : IsWitness p c) (hq : IsWitness q d) :
    IsWitness (p + q) (c + d) := by
  grind [IsWitness]

@[simp]
lemma IsWitness.zero : IsWitness (0 : Meldable.Placement n) (0 : Hand n) := by simp [IsWitness]

@[grind ←]
lemma IsWitness.nsmul {p : Meldable.Placement n} {c : Hand n}
    (hp : IsWitness p c) (k : ℕ) : IsWitness (k • p) (k • c) := by
  grind [IsWitness]

end Meldable

def Meldable (c : Hand n) : Prop := ∃ p : Meldable.Placement n, Meldable.IsWitness p c

namespace Meldable

@[simp]
lemma sequence {i : Fin (3 * n - 2)} : Meldable (sequence i) := by
  refine ⟨Placement.ofFn 0 (fun j ↦ if j = i then 1 else 0), ?_⟩
  unfold IsWitness
  rw [Placement.toHand_eq_sum]
  simp

@[simp]
lemma triplet {i : Fin (3 * n)} : Meldable (triplet i) := by
  refine ⟨Placement.ofFn (fun j ↦ if j = i then 1 else 0) 0, ?_⟩
  unfold IsWitness
  rw [Placement.toHand_eq_sum]
  simp

@[grind ←]
lemma add {c d : Hand n} (hc : Meldable c) (hd : Meldable d) :
    Meldable (c + d) := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq⟩ := hd
  exact ⟨p + q, hp.add hq⟩

@[simp]
lemma zero : Meldable (0 : Hand n) := ⟨0, IsWitness.zero⟩

@[grind ←]
lemma nsmul {c : Hand n} (hc : Meldable c) (a : ℕ) :
    Meldable (a • c) := by
  obtain ⟨p, hp⟩ := hc
  exact ⟨a • p, hp.nsmul a⟩

lemma finset_sum {ι : Type*} {s : Finset ι} {f : ι → Hand n}
    (hf : ∀ i ∈ s, Meldable (f i)) : Meldable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        Meldable.add (hf i (Finset.mem_insert_self i s))
          (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[grind →]
theorem size_mod_three {c : Hand n} (hc : Meldable c) :
    size c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, size_triplet, size_sequence, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

@[grind →]
theorem sum_mod_three {c : Hand n} (hc : Meldable c) :
    sum c % 3 = 0 := by
  obtain ⟨p, rfl⟩ := hc
  rw [Placement.toHand_eq_sum, map_add, map_sum, map_sum]
  simp only [map_nsmul, sum_triplet, sum_sequence, smul_eq_mul]
  simp_rw [mul_comm 3, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, Nat.mul_mod_left]

end Meldable

def Winning (c : Hand n) : Prop :=
  Valid c ∧ size c = 3 * n + 5 ∧
    ∃ (d : Hand n) (i : Fin (3 * n)), Meldable d ∧ c = d + pair i

@[grind →]
lemma Winning.size {c : Hand n} (hc : Winning c) : size c = 3 * n + 5 := hc.2.1

def IsWinningTile (c : Hand n) (i : Fin (3 * n)) : Prop := Winning (c + single i)

def IsWait (c : Hand n) : Prop := ∃ i, Winning (c + single i)

@[grind →]
lemma IsWait.Valid (c : Hand n) (hc : IsWait c) : Valid c := by
  grind [IsWait, Winning, Valid]

def IsFullWait (c : Hand n) : Prop := ∀ i, Winning (c + single i)

@[grind →]
lemma IsFullWait.size (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    size c = 3 * n + 4 := by
  let i : Fin (3 * n) := ⟨0, by omega⟩
  have hsize := (hc i).size
  grind

def filter (keep : ℤ → Prop) [DecidablePred keep] : Hand n →+ Hand n where
  toFun c := Hand.ofFn fun i ↦ if keep i.val then c.count i else 0
  map_zero' := by
    congr
    funext i
    split <;> rfl
  map_add' _ _ := by
    change ofFn _ = ofFn _
    congr 1
    funext i
    change (if keep i.val then _ + _ else 0) =
      (if keep i.val then _ else 0) + if keep i.val then _ else 0
    split <;> simp_all

@[simp, grind =]
theorem filter_apply (keep : ℤ → Prop) [DecidablePred keep]
    (c : Hand n) (i : ℤ) :
    filter keep c i = if keep i then c i else 0 := by
  change extend (filter keep c).count i = if keep i then extend c.count i else 0
  unfold filter Hand.ofFn
  exact extend_filter _ _ _

namespace Meldable.Placement

def filter
    (tripKeep seqKeep : ℤ → Prop) [DecidablePred tripKeep] [DecidablePred seqKeep] :
    Placement n →+ Placement n where
  toFun p := Placement.ofFn
    (fun i ↦ if tripKeep i.val then p.tripNum i.val else 0)
    (fun i ↦ if seqKeep i.val then p.seqNum i.val else 0)
  map_zero' := by
    change ofFn _ _ = ofFn _ _
    congr 1 <;> funext i <;> simp
  map_add' _ _ := by
    change ofFn _ _ = ofFn _ _
    congr 1 <;> funext i
    all_goals split <;> simp_all [ofFn]

@[simp, grind =]
theorem tripNum_filter (tripKeep seqKeep : ℤ → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : ℤ) :
    (filter tripKeep seqKeep p).tripNum i =
      if tripKeep i then p.tripNum i else 0 := by
  simpa [filter, tripNum, ofFn] using extend_filter p.tripNum' tripKeep i

@[simp, grind =]
theorem seqNum_filter (tripKeep seqKeep : ℤ → Prop)
    [DecidablePred tripKeep] [DecidablePred seqKeep]
    (p : Placement n) (i : ℤ) :
    (filter tripKeep seqKeep p).seqNum i =
      if seqKeep i then p.seqNum i else 0 := by
  simpa [filter, seqNum, ofFn] using extend_filter p.seqNum' seqKeep i

end Meldable.Placement

end Hand

end Mahjong
