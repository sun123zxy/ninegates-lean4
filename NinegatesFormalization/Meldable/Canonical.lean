import NinegatesFormalization.Meldable.Basic

/-!
# Canonical meld decompositions

## Main Definitions

- `Placement.Canonical p` means that fewer than three sequences start at each
  coordinate.

- `p.canonicalize` reduces the number of sequences at each starting coordinate
  modulo three.  Each removed group of three equal sequences is replaced by one
  triplet at each of the three coordinates covered by those sequences.

## Main Results

- `p.canonicalize` is canonical and gives the same hand as `p`.
- `canonicalize` fixes exactly the canonical placements and is idempotent.
- Two canonical placements giving the same hand are equal.
- A hand is `Meldable` if and only if it has a canonical witness.
-/

namespace Mahjong.Hand.Meldable

namespace Placement

variable {n : ℕ}

/-- A placement is canonical when it uses fewer than three sequences at every start. -/
def Canonical (p : Placement n) : Prop := ∀ i : ℤ, p.seqNum i < 3

/-- Replace groups of three equal sequences by the corresponding triplets. -/
def canonicalize (p : Placement n) : Placement n :=
  ofFn
    (fun i ↦
      p.tripNum i.val + p.seqNum i.val / 3 +
        p.seqNum (i.val - 1) / 3 +
        p.seqNum (i.val - 2) / 3)
    (fun i ↦ p.seqNum i.val % 3)

@[simp, grind =]
lemma tripNum_canonicalize (p : Placement n) (i : ℤ) :
    p.canonicalize.tripNum i =
      p.tripNum i + p.seqNum i / 3 +
        p.seqNum (i - 1) / 3 + p.seqNum (i - 2) / 3 := by
  grind [= canonicalize]

@[simp, grind =]
lemma seqNum_canonicalize (p : Placement n) (i : ℤ) :
    p.canonicalize.seqNum i = p.seqNum i % 3 := by
  grind [= canonicalize]

@[simp]
lemma Canonical.canonicalize (p : Placement n) : p.canonicalize.Canonical := by
  grind [= Canonical]

@[simp]
theorem toHand_canonicalize (p : Placement n) :
    p.canonicalize.toHand = p.toHand := by
  ext i
  grind

theorem Canonical.iff_canonicalize_eq_self (p : Placement n) :
    p.Canonical ↔ p.canonicalize = p := by
  grind [= Canonical]

@[simp]
theorem canonicalize_idem (p : Placement n) :
    p.canonicalize.canonicalize = p.canonicalize := by
  exact (Canonical.iff_canonicalize_eq_self p.canonicalize).mp
    (Canonical.canonicalize p)

theorem Canonical.unique {p q : Placement n}
    (hp : p.Canonical) (hq : q.Canonical) (h : p.toHand = q.toHand) :
    p = q := by
  have hcoord : ∀ k : ℕ, k < 3 * n →
      p.tripNum k = q.tripNum k ∧ p.seqNum k = q.seqNum k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hprev₁ : p.seqNum ((k : ℤ) - 1) = q.seqNum ((k : ℤ) - 1) := by
        cases k with
        | zero => simp
        | succ k => simpa using (ih k (by omega) (by omega)).2
      have hprev₂ : p.seqNum ((k : ℤ) - 2) = q.seqNum ((k : ℤ) - 2) := by
        cases k with
        | zero => simp
        | succ k =>
          cases k with
          | zero => simp
          | succ k =>
            have hk : ((k + 1 + 1 : ℕ) : ℤ) - 2 = k := by omega
            simpa only [hk] using (ih k (by omega) (by omega)).2
      have hhand := congrArg (fun c : Hand n ↦ c k) h
      simp only [toHand_apply] at hhand
      have hpk := hp k
      have hqk := hq k
      constructor <;> omega
  apply ext <;> intro i hi₀ hi₁
  · simpa [Int.toNat_of_nonneg hi₀] using (hcoord i.toNat (by omega)).1
  · simpa [Int.toNat_of_nonneg hi₀] using (hcoord i.toNat (by omega)).2

end Placement

variable {n : ℕ}

/-- A hand is meldable exactly when it has a canonical placement. -/
theorem iff_exists_canonical_witness (c : Hand n) :
    Meldable c ↔ ∃ p, IsWitness p c ∧ p.Canonical := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.canonicalize, ?_, Placement.Canonical.canonicalize p⟩
    simpa [IsWitness] using hp
  · rintro ⟨p, hp, _⟩
    exact ⟨p, hp⟩

end Mahjong.Hand.Meldable
