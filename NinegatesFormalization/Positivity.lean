import NinegatesFormalization.Split
import NinegatesFormalization.Winning

namespace Mahjong.Hand

variable {n : ℕ}

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k.val = 0) :
    (size (restrictLT k.val w) % 3 = 2 ∧
      size (restrictGT k.val w) % 3 = 0 ∧ Meldable (restrictGT k.val w)) ∨
    (size (restrictLT k.val w) % 3 = 0 ∧
      size (restrictGT k.val w) % 3 = 2 ∧ Meldable (restrictLT k.val w)) := by
  grind [Winning]

theorem interior_positive (hn : 2 ≤ n) (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i.val := by
  intro k hk
  by_contra hpositive
  have hck : c k.val = 0 := by grind
  let first : Fin (3 * n) := ⟨0, by omega⟩
  let last : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hfirst : first < k := by grind
  have hlast : k < last := by grind
  have hzero (i : Fin (3 * n)) (hi : i ≠ k) :
      (c + single i) k.val = 0 := by grind
  have hfirst_zero : (c + single first) k.val = 0 :=
    hzero first (ne_of_lt hfirst)
  have hlast_zero : (c + single last) k.val = 0 :=
    hzero last (ne_of_gt hlast)
  have hfirst_sides := winning_sides_at_zero (hc first) k hfirst_zero
  have hlast_sides := winning_sides_at_zero (hc last) k hlast_zero
  have hsizes : size (restrictLT k.val c) % 3 = 2 ∧
      size (restrictGT k.val c) % 3 = 2 := by grind
  have hleft_meldable (i : Fin (3 * n)) (hi : i < k) :
      Meldable (restrictLT k.val (c + single i)) := by
    have hi_zero : (c + single i) k.val = 0 := hzero i (ne_of_lt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides <;> grind
  have hright_meldable (i : Fin (3 * n)) (hi : k < i) :
      Meldable (restrictGT k.val (c + single i)) := by
    have hi_zero : (c + single i) k.val = 0 := hzero i (ne_of_gt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides <;> grind
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀ < k := by grind
    have hi₁ : i₁ < k := by grind
    have hsum₀ : (sum (restrictLT k.val c) + 0) % 3 = 0 := by grind
    have hsum₁ : (sum (restrictLT k.val c) + 1) % 3 = 0 := by grind
    grind
  · have hkval : k.val = 1 := by omega
    let i₂ : Fin (3 * n) := ⟨2, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    let i₃ : Fin (3 * n) := ⟨3, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    have hi₂ : k < i₂ := by grind
    have hi₃ : k < i₃ := by grind
    have hsum₂ : (sum (restrictGT k.val c) + 2) % 3 = 0 := by grind
    have hsum₃ : (sum (restrictGT k.val c) + 3) % 3 = 0 := by grind
    grind

end Mahjong.Hand
