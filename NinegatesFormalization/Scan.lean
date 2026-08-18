import NinegatesFormalization.Basic

namespace Mahjong.Hand

variable {n : ℕ}

private abbrev ScanState := ℕ × ℕ

private def stateAt (c : Hand n) : ℕ → ScanState
  | 0 => (0, 0)
  | i + 1 =>
      let s := c.stateAt i
      ((c i - (s.1 + s.2)) % 3, s.1)

private def residual (c : Hand n) (i : ℕ) : ℕ :=
  let s := c.stateAt i
  c i - (s.1 + s.2)

def canonicalPlacement (c : Hand n) : Meldable.Placement n :=
  Meldable.Placement.ofFn
    (fun i ↦ c.residual i.val / 3)
    (fun i ↦ c.residual i.val % 3)

namespace Meldable.ScanMonadFree

open Placement

private lemma stateAt_toHand (p : Placement n) (i : ℕ) :
    p.toHand.stateAt i =
      (p.seqNum ((i : ℤ) - 1) % 3, p.seqNum ((i : ℤ) - 2) % 3) := by
  induction i with
  | zero => simp [stateAt]
  | succ i ih =>
      simp only [stateAt, ih, Placement.toHand_apply]
      have h₁ : ((i + 1 : ℕ) : ℤ) - 1 = i := by omega
      have h₂ : ((i + 1 : ℕ) : ℤ) - 2 = (i : ℤ) - 1 := by omega
      simp only [h₁, h₂]
      congr 1
      omega

private lemma residual_toHand (p : Placement n) (i : ℕ) :
    p.toHand.residual i =
      3 * (p.tripNum i + p.seqNum i / 3 +
        p.seqNum ((i : ℤ) - 1) / 3 + p.seqNum ((i : ℤ) - 2) / 3) +
          p.seqNum i % 3 := by
  simp only [residual, stateAt_toHand, Placement.toHand_apply]
  omega

@[local grind =]
private lemma canonical_tripNum (p : Placement n) (i : ℤ) :
    p.toHand.canonicalPlacement.tripNum i =
      p.tripNum i + p.seqNum i / 3 +
        p.seqNum (i - 1) / 3 + p.seqNum (i - 2) / 3 := by
  simp only [canonicalPlacement, Placement.tripNum_ofFn]
  split
  next h =>
    have hi : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h.1
    simp only [residual_toHand, hi]
    omega
  next h => grind

@[local grind =]
private lemma canonical_seqNum (p : Placement n) (i : ℤ) :
    p.toHand.canonicalPlacement.seqNum i = p.seqNum i % 3 := by
  simp only [canonicalPlacement, Placement.seqNum_ofFn]
  split
  next h =>
    have hi : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h.1
    simp only [residual_toHand, hi]
    omega
  next h => grind

private theorem canonical_toHand (p : Placement n) :
    p.toHand.canonicalPlacement.toHand = p.toHand := by
  apply Hand.ext
  intro i
  simp only [Placement.toHand_apply, canonical_tripNum, canonical_seqNum]
  omega

theorem iff_canonical (c : Hand n) :
    Meldable c ↔ c.canonicalPlacement.toHand = c := by
  constructor
  · rintro ⟨p, rfl⟩
    exact canonical_toHand p
  · exact fun h ↦ ⟨c.canonicalPlacement, h⟩

end Meldable.ScanMonadFree

end Mahjong.Hand
