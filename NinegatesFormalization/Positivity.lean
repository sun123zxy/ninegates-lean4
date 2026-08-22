import NinegatesFormalization.Split
import NinegatesFormalization.Winning

namespace Mahjong.Hand

variable {n : ℕ}

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k = 0) :
    (size (restrictLT k w) % 3 = 2 ∧
      size (restrictGT k w) % 3 = 0 ∧ Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧
      size (restrictGT k w) % 3 = 2 ∧ Meldable (restrictLT k w)) := by
  grind [Winning, → Meldable.split_at_zero, → Meldable.size_mod_three]

theorem interior_positive (hn : 2 ≤ n) (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i := by
  intro k hk
  by_contra hpositive
  have hck : c k = 0 := by grind
  let first : Fin (3 * n) := ⟨0, by omega⟩
  let last : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hfirst : first.val < k.val := by grind
  have hlast : k.val < last.val := by grind
  have hzero (i : Fin (3 * n)) (hi : i.val ≠ k.val) :
      (c + single i) k = 0 := by grind
  have hfirst_zero : (c + single first) k = 0 :=
    hzero first (ne_of_lt hfirst)
  have hlast_zero : (c + single last) k = 0 :=
    hzero last (ne_of_gt hlast)
  have hfirst_sides := winning_sides_at_zero (hc first) k hfirst_zero
  have hlast_sides := winning_sides_at_zero (hc last) k hlast_zero
  have hsizes : size (restrictLT k c) % 3 = 2 ∧
      size (restrictGT k c) % 3 = 2 := by grind
  have hleft_meldable (i : Fin (3 * n)) (hi : i.val < k.val) :
      Meldable (restrictLT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_lt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides <;> grind
  have hright_meldable (i : Fin (3 * n)) (hi : k.val < i.val) :
      Meldable (restrictGT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_gt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides <;> grind
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀.val < k.val := by grind
    have hi₁ : i₁.val < k.val := by grind
    have hsum₀ : (sum (restrictLT k c) + 0) % 3 = 0 := by
      simpa [restrictLT_single_of_lt k i₀ hi₀, i₀] using
        Meldable.sum_mod_three (hleft_meldable i₀ hi₀)
    have hsum₁ : (sum (restrictLT k c) + 1) % 3 = 0 := by
      simpa [restrictLT_single_of_lt k i₁ hi₁, i₁] using
        Meldable.sum_mod_three (hleft_meldable i₁ hi₁)
    grind
  · have hkval : k.val = 1 := by omega
    let i₂ : Fin (3 * n) := ⟨2, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    let i₃ : Fin (3 * n) := ⟨3, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    have hi₂ : k.val < i₂.val := by grind
    have hi₃ : k.val < i₃.val := by grind
    have hsum₂ : (sum (restrictGT k c) + 2) % 3 = 0 := by
      simpa [restrictGT_single_of_gt k i₂ hi₂, i₂] using
        Meldable.sum_mod_three (hright_meldable i₂ hi₂)
    have hsum₃ : (sum (restrictGT k c) + 3) % 3 = 0 := by
      simpa [restrictGT_single_of_gt k i₃ hi₃, i₃] using
        Meldable.sum_mod_three (hright_meldable i₃ hi₃)
    grind

end Mahjong.Hand
