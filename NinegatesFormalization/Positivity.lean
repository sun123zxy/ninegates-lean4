import NinegatesFormalization.Split

namespace Mahjong.Hand

variable {n : ℕ}

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k = 0) :
    (size (restrictLT k w) % 3 = 2 ∧
      size (restrictGT k w) % 3 = 0 ∧ Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧
      size (restrictGT k w) % 3 = 2 ∧ Meldable (restrictLT k w)) := by
  obtain ⟨_, _, d, p, hd, hwd⟩ := hw
  have hdk : d k = 0 := by grind
  have hpair : pair p k = 0 := by grind
  have hpk : p ≠ k := by grind
  have ⟨hdLT, hdGT⟩ := hd.split_at_zero k hdk
  rcases lt_or_gt_of_ne hpk with hleft | hright
  · left
    have hLT : restrictLT k w = restrictLT k d + pair p := by grind
    have hGT : restrictGT k w = restrictGT k d := by grind
    rw [hLT, hGT]
    refine ⟨?_, hdGT.size_mod_three, hdGT⟩
    grind
  · right
    have hLT : restrictLT k w = restrictLT k d := by grind
    have hGT : restrictGT k w = restrictGT k d + pair p := by grind
    rw [hLT, hGT]
    grind

theorem interior_positive (hn : 2 ≤ n) (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i := by
  intro k hk
  by_contra hpositive
  have hck : c k = 0 := by grind
  let first : Fin (3 * n) := ⟨0, by omega⟩
  let last : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hfirst : first < k := by grind
  have hlast : k < last := by grind
  have hzero (i : Fin (3 * n)) (hi : i ≠ k) : (c + single i) k = 0 := by grind
  have hfirst_zero : (c + single first) k = 0 := hzero first (ne_of_lt hfirst)
  have hlast_zero : (c + single last) k = 0 := hzero last (ne_of_gt hlast)
  have hfirst_sides := winning_sides_at_zero (hc first) k hfirst_zero
  have hlast_sides := winning_sides_at_zero (hc last) k hlast_zero
  have hsizes : size (restrictLT k c) % 3 = 2 ∧ size (restrictGT k c) % 3 = 2 := by grind
  have hleft_meldable (i : Fin (3 * n)) (hi : i < k) :
      Meldable (restrictLT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_lt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides <;> grind
  have hright_meldable (i : Fin (3 * n)) (hi : k < i) :
      Meldable (restrictGT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_gt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides <;> grind
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀ < k := by grind
    have hi₁ : i₁ < k := by grind
    have hsum₀ : (sum (restrictLT k c) + 0) % 3 = 0 := by grind
    have hsum₁ : (sum (restrictLT k c) + 1) % 3 = 0 := by grind
    omega
  · have hkval : k.val = 1 := by omega
    let i₂ : Fin (3 * n) := ⟨2, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    let i₃ : Fin (3 * n) := ⟨3, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    have hi₂ : k < i₂ := by grind
    have hi₃ : k < i₃ := by grind
    have hsum₂ : (sum (restrictGT k c) + 2) % 3 = 0 := by grind
    have hsum₃ : (sum (restrictGT k c) + 3) % 3 = 0 := by grind
    omega

end Mahjong.Hand
