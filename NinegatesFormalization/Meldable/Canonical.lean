import NinegatesFormalization.Meldable.Basic

/-!
# Canonical meld decompositions

## Main definitions

- `Placement.Canonical p` means that fewer than three sequences start at each
  coordinate.

- `p.canonicalize` reduces the number of sequences at each starting coordinate
  modulo three.  Each removed group of three equal sequences is replaced by one
  triplet at each of the three coordinates covered by those sequences.

## Main results

- `p.canonicalize` is canonical and gives the same hand as `p`.
- `canonicalize` fixes exactly the canonical placements and is idempotent.
- Two canonical placements giving the same hand are equal.
- A hand is `Meldable` if and only if it has a canonical witness.
-/

namespace Mahjong.Hand.Meldable

namespace Placement

variable {n : ℕ}

/-- A placement is canonical when it uses fewer than three sequences at every start. -/
@[grind =]
def Canonical (p : Placement n) : Prop := ∀ i, p.seqNum i < 3

/-- Replace groups of three equal sequences by the corresponding triplets. -/
def canonicalize (p : Placement n) : Placement n :=
  ⟨(fun i ↦
      p.tripNum i + p.seqNum i / 3 +
        (if 1 ≤ i.val then p.seqNum ⟨i.val - 1, by omega⟩ / 3 else 0) +
        (if 2 ≤ i.val then p.seqNum ⟨i.val - 2, by omega⟩ / 3 else 0)),
    (fun i ↦ p.seqNum i % 3), by
      constructor <;> intro i hi <;> grind⟩

@[grind =]
lemma tripNum_canonicalize (p : Placement n) (i : Fin (3 * n)) :
    p.canonicalize.tripNum i =
      p.tripNum i + p.seqNum i / 3 +
        (if 1 ≤ i.val then p.seqNum ⟨i.val - 1, by omega⟩ / 3 else 0) +
        (if 2 ≤ i.val then p.seqNum ⟨i.val - 2, by omega⟩ / 3 else 0) := rfl

@[simp, grind =]
lemma seqNum_canonicalize (p : Placement n) (i : Fin (3 * n)) :
    p.canonicalize.seqNum i = p.seqNum i % 3 := rfl

@[simp, grind =]
lemma tripNum_canonicalize_of_eq_zero (p : Placement n) (i : Fin (3 * n))
    (hi : i.val = 0) :
    p.canonicalize.tripNum i = p.tripNum i + p.seqNum i / 3 := by grind

@[simp, grind =]
lemma tripNum_canonicalize_of_eq_one (p : Placement n) (i : Fin (3 * n))
    (hi : i.val = 1) :
    p.canonicalize.tripNum i = p.tripNum i + p.seqNum i / 3 +
      p.seqNum ⟨0, by omega⟩ / 3 := by grind

@[simp, grind =]
lemma tripNum_canonicalize_of_ge_two (p : Placement n) (i : Fin (3 * n))
    (hi : 2 ≤ i.val) :
    p.canonicalize.tripNum i = p.tripNum i + p.seqNum i / 3 +
      p.seqNum ⟨i.val - 1, by omega⟩ / 3 +
      p.seqNum ⟨i.val - 2, by omega⟩ / 3 := by grind

lemma Canonical.canonicalize (p : Placement n) : p.canonicalize.Canonical := by
  grind

@[simp, grind =]
theorem toHand_canonicalize (p : Placement n) : p.canonicalize.toHand = p.toHand := by
  ext i; grind

theorem Canonical.iff_canonicalize_eq_self (p : Placement n) :
    p.Canonical ↔ p.canonicalize = p := by
  constructor
  · intro hp
    ext i <;> grind
  · intro h i
    have hi := congrArg (fun q : Placement n ↦ q.seqNum i) h
    grind

@[simp, grind =]
theorem canonicalize_idem (p : Placement n) :
    p.canonicalize.canonicalize = p.canonicalize := by
  exact (Canonical.iff_canonicalize_eq_self p.canonicalize).mp
    (Canonical.canonicalize p)

theorem Canonical.unique {p q : Placement n}
    (hp : p.Canonical) (hq : q.Canonical) (h : p.toHand = q.toHand) :
    p = q := by
  have hcoord : ∀ k : ℕ, ∀ hk : k < 3 * n,
      p.tripNum ⟨k, hk⟩ = q.tripNum ⟨k, hk⟩ ∧
        p.seqNum ⟨k, hk⟩ = q.seqNum ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let i : Fin (3 * n) := ⟨k, hk⟩
      have hhand := congrArg (fun c : Hand n ↦ c i) h
      have hpk := hp i
      have hqk := hq i
      by_cases hk₀ : k = 0
      · constructor <;> grind
      by_cases hk₁ : k = 1
      · have hprev := (ih 0 (by omega) (by omega)).2
        constructor <;> grind
      · have hprev₁ := (ih (k - 1) (by omega) (by omega)).2
        have hprev₂ := (ih (k - 2) (by omega) (by omega)).2
        constructor <;> grind
  ext i
  · exact (hcoord i.val i.isLt).1
  · exact (hcoord i.val i.isLt).2

end Placement

variable {n : ℕ}

theorem toHand_iff_witness_canonicalize (p : Placement n) :
    Meldable p.toHand ↔ IsWitness p.canonicalize p.toHand := by
  constructor
  · rintro ⟨q, hq⟩
    rw [IsWitness, Placement.toHand_canonicalize]
  · rintro h
    exact ⟨p.canonicalize, h⟩

/-- A hand is meldable exactly when it has a canonical placement. -/
theorem iff_exists_canonical_witness (c : Hand n) :
    Meldable c ↔ ∃ p, IsWitness p c ∧ p.Canonical := by
  constructor
  · rintro ⟨p, hp⟩
    use p.canonicalize, ?_, Placement.Canonical.canonicalize p
    rw [IsWitness, Placement.toHand_canonicalize, hp]
  · rintro ⟨p, hp, _⟩
    exact ⟨p, hp⟩

end Mahjong.Hand.Meldable
