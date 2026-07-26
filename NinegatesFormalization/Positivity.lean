import NinegatesFormalization.Split

namespace Mahjong.Hand

variable {n : ℕ}

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : count k w = 0) :
    (size (restrictLT k w) % 3 = 2 ∧
      size (restrictGT k w) % 3 = 0 ∧ Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧
      size (restrictGT k w) % 3 = 2 ∧ Meldable (restrictLT k w)) := by
  obtain ⟨_, _, d, p, hd, hwd⟩ := hw
  have hzero : count k d + count k (pair p) = 0 := by grind
  have hdk : count k d = 0 := by omega
  have hpair : count k (pair p) = 0 := by omega
  have hpk : p ≠ k := by
    rintro rfl
    simp [pair] at hpair
  have ⟨hdLT, hdGT⟩ := hd.split_at_zero k hdk
  rcases lt_or_gt_of_ne hpk with hleft | hright
  · left
    have hLT : restrictLT k w = restrictLT k d + pair p := by
      rw [hwd, map_add, restrictLT_pair_of_lt _ _ hleft]
    have hGT : restrictGT k w = restrictGT k d := by
      simp only [hwd, map_add,
        restrictGT_pair_of_not_gt _ _ (not_lt_of_ge (le_of_lt hleft)), add_zero]
    rw [hLT, hGT]
    refine ⟨?_, hdGT.size_mod_three, hdGT⟩
    grind
  · right
    have hLT : restrictLT k w = restrictLT k d := by
      simp only [hwd, map_add,
        restrictLT_pair_of_not_lt _ _ (not_lt_of_ge (le_of_lt hright)), add_zero]
    have hGT : restrictGT k w = restrictGT k d + pair p := by
      rw [hwd, map_add, restrictGT_pair_of_gt _ _ hright]
    rw [hLT, hGT]
    grind

theorem interior_positive (hn : 2 ≤ n) (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i := by
  intro k hk
  by_contra hpositive
  have hck : count k c = 0 := by grind
  let first : Fin (3 * n) := ⟨0, by omega⟩
  let last : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hfirst : first < k := by
    exact Fin.mk_lt_mk.mpr hk.1
  have hlast : k < last := by
    exact Fin.mk_lt_mk.mpr hk.2
  have hzero (i : Fin (3 * n)) (hi : i ≠ k) :
      count k (c + single i) = 0 := by
    grind
  have hfirst_zero : count k (c + single first) = 0 :=
    hzero first (ne_of_lt hfirst)
  have hlast_zero : count k (c + single last) = 0 :=
    hzero last (ne_of_gt hlast)
  have hfirst_sides := winning_sides_at_zero (hc first) k hfirst_zero
  have hlast_sides := winning_sides_at_zero (hc last) k hlast_zero
  simp only [map_add, restrictLT_single_of_lt _ _ hfirst,
    restrictGT_single_of_not_gt _ _
      (not_lt_of_ge (le_of_lt hfirst)), add_zero, size_single] at hfirst_sides
  simp only [map_add,
    restrictLT_single_of_not_lt _ _
      (not_lt_of_ge (le_of_lt hlast)), add_zero,
    restrictGT_single_of_gt _ _ hlast, size_single] at hlast_sides
  have hsizes :
      size (restrictLT k c) % 3 = 2 ∧ size (restrictGT k c) % 3 = 2 := by
    grind
  have hleft_meldable (i : Fin (3 * n)) (hi : i < k) :
      Meldable (restrictLT k (c + single i)) := by
    have hi_zero : count k (c + single i) = 0 := hzero i (ne_of_lt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides
    · have hsize := hsides.1
      simp only [map_add, restrictLT_single_of_lt _ _ hi, size_single] at hsize
      grind
    · exact hsides.2.2
  have hright_meldable (i : Fin (3 * n)) (hi : k < i) :
      Meldable (restrictGT k (c + single i)) := by
    have hi_zero : count k (c + single i) = 0 := hzero i (ne_of_gt hi)
    rcases winning_sides_at_zero (hc i) k hi_zero with hsides | hsides
    · exact hsides.2.2
    · have hsize := hsides.2.1
      simp only [map_add, restrictGT_single_of_gt _ _ hi, size_single] at hsize
      grind
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀ < k := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hi₁ : i₁ < k := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hsum₀ : (sum (restrictLT k c) + 0) % 3 = 0 := by
      have := hleft_meldable i₀ hi₀
      grind
    have hsum₁ : (sum (restrictLT k c) + 1) % 3 = 0 := by
      have := hleft_meldable i₁ hi₁
      grind
    omega
  · have hkval : k.val = 1 := by omega
    let i₂ : Fin (3 * n) :=
      ⟨2, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    let i₃ : Fin (3 * n) :=
      ⟨3, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    have hi₂ : k < i₂ := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hi₃ : k < i₃ := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hsum₂ : (sum (restrictGT k c) + 2) % 3 = 0 := by
      have := hright_meldable i₂ hi₂
      grind
    have hsum₃ : (sum (restrictGT k c) + 3) % 3 = 0 := by
      have := hright_meldable i₃ hi₃
      grind
    omega

end Mahjong.Hand
