import Mathlib
import NinegatesFormalization.Meldable

namespace Mahjong.Hand

variable {n : ℕ}

private lemma restrictLT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n))
    (hi : i < k) :
    restrictLT k (c + single i) = restrictLT k c + single i := by
  ext x
  by_cases hx : x < k
  · simp [hx]
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact hx hi
    simp [hx, hxi]

private lemma restrictGT_add_single_of_lt (c : Hand n) (k i : Fin (3 * n))
    (hi : i < k) :
    restrictGT k (c + single i) = restrictGT k c := by
  ext x
  by_cases hx : k < x
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact (not_lt_of_ge (le_of_lt hi)) hx
    simp [hx, hxi]
  · simp [hx]

private lemma restrictLT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n))
    (hi : k < i) :
    restrictLT k (c + single i) = restrictLT k c := by
  ext x
  by_cases hx : x < k
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact (not_lt_of_ge (le_of_lt hi)) hx
    simp [hx, hxi]
  · simp [hx]

private lemma restrictGT_add_single_of_gt (c : Hand n) (k i : Fin (3 * n))
    (hi : k < i) :
    restrictGT k (c + single i) = restrictGT k c + single i := by
  ext x
  by_cases hx : k < x
  · simp [hx]
  · have hxi : x ≠ i := by
      intro h
      subst x
      exact hx hi
    simp [hx, hxi]

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k = 0) :
    (size (restrictLT k w) % 3 = 2 ∧
      size (restrictGT k w) % 3 = 0 ∧ Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧
      size (restrictGT k w) % 3 = 2 ∧ Meldable (restrictLT k w)) := by
  obtain ⟨_, d, p, hd, hwd⟩ := hw
  have hzero : d k + pair p k = 0 := by
    rw [hwd] at hk
    exact hk
  have hdk : d k = 0 := Nat.eq_zero_of_add_eq_zero_right hzero
  have hpair : pair p k = 0 := Nat.eq_zero_of_add_eq_zero_left hzero
  have hpk : p ≠ k := by
    intro h
    subst p
    simp [pair] at hpair
  obtain ⟨hdLT, hdGT⟩ := hd.split_at_zero k hdk
  rcases lt_or_gt_of_ne hpk with hleft | hright
  · left
    have hLT : restrictLT k w = restrictLT k d + pair p := by
      ext x
      by_cases hx : x < k
      · simp [hwd, hx]
      · have hxp : x ≠ p := by
          intro h
          subst x
          exact hx hleft
        simp [hwd, hx, hxp, pair]
    have hGT : restrictGT k w = restrictGT k d := by
      ext x
      by_cases hx : k < x
      · have hxp : x ≠ p := by
          intro h
          subst x
          exact (not_lt_of_ge (le_of_lt hleft)) hx
        simp [hwd, hx, hxp, pair]
      · simp [hwd, hx]
    rw [hLT, hGT]
    refine ⟨?_, hdGT.size_mod_three, hdGT⟩
    rw [size_add, size_pair]
    rw [Nat.add_mod, hdLT.size_mod_three]
  · right
    have hLT : restrictLT k w = restrictLT k d := by
      ext x
      by_cases hx : x < k
      · have hxp : x ≠ p := by
          intro h
          subst x
          exact (not_lt_of_ge (le_of_lt hright)) hx
        simp [hwd, hx, hxp, pair]
      · simp [hwd, hx]
    have hGT : restrictGT k w = restrictGT k d + pair p := by
      ext x
      by_cases hx : k < x
      · simp [hwd, hx]
      · have hxp : x ≠ p := by
          intro h
          subst x
          exact hx hright
        simp [hwd, hx, hxp, pair]
    rw [hLT, hGT]
    refine ⟨hdLT.size_mod_three, ?_, hdLT⟩
    rw [size_add, size_pair]
    rw [Nat.add_mod, hdGT.size_mod_three]

variable {n : ℕ} (hn : 2 ≤ n)

include hn in
theorem interior_positive (c : Hand n) (hc : IsFullWait c) :
    ∀ i : Fin (3 * n), 0 < i.val ∧ i.val < 3 * n - 1 → 0 < c i := by
  intro k hk
  by_contra hpositive
  have hck : c k = 0 := by omega
  let first : Fin (3 * n) := ⟨0, by omega⟩
  let last : Fin (3 * n) := ⟨3 * n - 1, by omega⟩
  have hfirst : first < k := by
    change 0 < k.val
    exact hk.1
  have hlast : k < last := by
    change k.val < 3 * n - 1
    exact hk.2
  have hzero (i : Fin (3 * n)) (hi : i ≠ k) : (c + single i) k = 0 := by
    simp [hck, Ne.symm hi]
  have hfirst_zero : (c + single first) k = 0 :=
    hzero first (ne_of_lt hfirst)
  have hlast_zero : (c + single last) k = 0 :=
    hzero last (ne_of_gt hlast)
  have hfirst_sides := winning_sides_at_zero (hc first) k hfirst_zero
  have hlast_sides := winning_sides_at_zero (hc last) k hlast_zero
  rw [restrictLT_add_single_of_lt c k first hfirst,
    restrictGT_add_single_of_lt c k first hfirst,
    size_add, size_single] at hfirst_sides
  rw [restrictLT_add_single_of_gt c k last hlast,
    restrictGT_add_single_of_gt c k last hlast,
    size_add, size_single] at hlast_sides
  have hsizes :
      size (restrictLT k c) % 3 = 2 ∧ size (restrictGT k c) % 3 = 2 := by
    rcases hfirst_sides with hfirst_sides | hfirst_sides <;>
      rcases hlast_sides with hlast_sides | hlast_sides <;> omega
  have hleft_meldable (i : Fin (3 * n)) (hi : i < k) :
      Meldable (restrictLT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_lt hi)
    have hsides := winning_sides_at_zero (hc i) k hi_zero
    rw [restrictLT_add_single_of_lt c k i hi,
      restrictGT_add_single_of_lt c k i hi,
      size_add, size_single] at hsides
    rcases hsides with hsides | hsides
    · omega
    · simpa only [restrictLT_add_single_of_lt c k i hi] using hsides.2.2
  have hright_meldable (i : Fin (3 * n)) (hi : k < i) :
      Meldable (restrictGT k (c + single i)) := by
    have hi_zero : (c + single i) k = 0 := hzero i (ne_of_gt hi)
    have hsides := winning_sides_at_zero (hc i) k hi_zero
    rw [restrictLT_add_single_of_gt c k i hi,
      restrictGT_add_single_of_gt c k i hi,
      size_add, size_single] at hsides
    rcases hsides with hsides | hsides
    · simpa only [restrictGT_add_single_of_gt c k i hi] using hsides.2.2
    · omega
  by_cases hkleft : 2 ≤ k.val
  · let i₀ : Fin (3 * n) := ⟨0, by omega⟩
    let i₁ : Fin (3 * n) := ⟨1, by omega⟩
    have hi₀ : i₀ < k := by
      change 0 < k.val
      omega
    have hi₁ : i₁ < k := by
      change 1 < k.val
      omega
    have hsum₀ := (hleft_meldable i₀ hi₀).sum_mod_three
    have hsum₁ := (hleft_meldable i₁ hi₁).sum_mod_three
    rw [restrictLT_add_single_of_lt c k i₀ hi₀, sum_add, sum_single] at hsum₀
    rw [restrictLT_add_single_of_lt c k i₁ hi₁, sum_add, sum_single] at hsum₁
    change (sum (restrictLT k c) + 0) % 3 = 0 at hsum₀
    change (sum (restrictLT k c) + 1) % 3 = 0 at hsum₁
    omega
  · have hkval : k.val = 1 := by omega
    let i₂ : Fin (3 * n) :=
      ⟨2, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    let i₃ : Fin (3 * n) :=
      ⟨3, lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_left 3 hn)⟩
    have hi₂ : k < i₂ := by
      change k.val < 2
      omega
    have hi₃ : k < i₃ := by
      change k.val < 3
      omega
    have hsum₂ := (hright_meldable i₂ hi₂).sum_mod_three
    have hsum₃ := (hright_meldable i₃ hi₃).sum_mod_three
    rw [restrictGT_add_single_of_gt c k i₂ hi₂, sum_add, sum_single] at hsum₂
    rw [restrictGT_add_single_of_gt c k i₃ hi₃, sum_add, sum_single] at hsum₃
    change (sum (restrictGT k c) + 2) % 3 = 0 at hsum₂
    change (sum (restrictGT k c) + 3) % 3 = 0 at hsum₃
    omega

end Mahjong.Hand
