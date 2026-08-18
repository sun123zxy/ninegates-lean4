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
        p.seqNum ((i.val : ℤ) - 1) / 3 +
        p.seqNum ((i.val : ℤ) - 2) / 3)
    (fun i ↦ p.seqNum i.val % 3)

@[simp]
lemma tripNum_canonicalize (p : Placement n) (i : ℤ) :
    p.canonicalize.tripNum i =
      p.tripNum i + p.seqNum i / 3 +
        p.seqNum (i - 1) / 3 + p.seqNum (i - 2) / 3 := by
  sorry

@[simp]
lemma seqNum_canonicalize (p : Placement n) (i : ℤ) :
    p.canonicalize.seqNum i = p.seqNum i % 3 := by
  sorry

lemma Canonical.canonicalize (p : Placement n) : p.canonicalize.Canonical := by
  sorry

@[simp]
theorem toHand_canonicalize (p : Placement n) :
    p.canonicalize.toHand = p.toHand := by
  sorry

theorem Canonical.iff_canonicalize_eq_self (p : Placement n) :
    p.Canonical ↔ p.canonicalize = p := by
  sorry

@[simp]
theorem canonicalize_idem (p : Placement n) :
    p.canonicalize.canonicalize = p.canonicalize := by
  sorry

theorem Canonical.unique {p q : Placement n}
    (hp : p.Canonical) (hq : q.Canonical) (h : p.toHand = q.toHand) :
    p = q := by
  sorry

end Placement

variable {n : ℕ}

/-- A hand is meldable exactly when it has a canonical placement. -/
theorem iff_exists_canonical_witness (c : Hand n) :
    Meldable c ↔ ∃ p, IsWitness p c ∧ p.Canonical := by
  sorry

end Mahjong.Hand.Meldable
