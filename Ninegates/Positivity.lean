/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Meldable.Split
public import Ninegates.Wait.Basic

/-!
# Full-wait positivity

## Main results

- `interior_positive` shows that every non-boundary coordinate of a full wait
  is occupied, using the split-at-zero meldability result.
- `excess_eq_six` is the immediate corollary of `interior_positive` that
  restricts the sum of the interior excess to exactly six.
- `interior_excess_le_six` is the weaker inequality derived from `excess_eq_six`,
  which is used in the reduction step.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

private lemma winning_sides_at_zero {w : Hand n} (hw : Winning w)
    (k : Fin (3 * n)) (hk : w k = 0) :
    (size (restrictLT k w) % 3 = 2 ∧ size (restrictGT k w) % 3 = 0 ∧
      Meldable (restrictGT k w)) ∨
    (size (restrictLT k w) % 3 = 0 ∧ size (restrictGT k w) % 3 = 2 ∧
      Meldable (restrictLT k w)) := by
  grind [Winning, → Meldable.split_at_zero, → Meldable.size_mod_three]

theorem interior_positive (c : Hand n) (hc : IsFullWait c) :
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
    by_cases hn : 2 ≤ n
    · let i₂ : Fin (3 * n) := ⟨2, by omega⟩
      let i₃ : Fin (3 * n) := ⟨3, by omega⟩
      have hi₂ : k.val < i₂.val := by grind
      have hi₃ : k.val < i₃.val := by grind
      have hsum₂ : (sum (restrictGT k c) + 2) % 3 = 0 := by
        simpa [restrictGT_single_of_gt k i₂ hi₂, i₂] using
          Meldable.sum_mod_three (hright_meldable i₂ hi₂)
      have hsum₃ : (sum (restrictGT k c) + 3) % 3 = 0 := by
        simpa [restrictGT_single_of_gt k i₃ hi₃, i₃] using
          Meldable.sum_mod_three (hright_meldable i₃ hi₃)
      grind
    · have hnval : n = 1 := by omega
      subst n
      have hkone : k = ⟨1, by decide⟩ := Fin.ext hkval
      subst k
      have hright : c ⟨2, by decide⟩ % 3 = 2 := by
        have h := hsizes.2
        simp [size_eq_sum, Fin.sum_univ_succ] at h
        grind
      -- Drawing the middle tile forces the pair there, where only one tile is available.
      obtain ⟨_, d, p, hd, heq⟩ := hc ⟨1, by decide⟩
      have hsum := Meldable.sum_mod_three hd
      have hs := congrArg sum heq
      simp only [map_add, sum_single, sum_pair] at hs
      have hsc : sum c = 2 * c ⟨2, by decide⟩ := by
        simpa [sum_eq_sum, Fin.sum_univ_succ] using hck
      have hp := congrArg (fun w : Hand 1 => w p) heq
      grind

theorem excess_eq_six (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    c ⟨0, by omega⟩ + c ⟨3 * n - 1, by omega⟩ +
      ∑ i : Fin (3 * n - 2), (c ⟨i.val + 1, by omega⟩ - 1) = 6 := by
  have hpos := interior_positive c hc
  have hsize := IsFullWait.size (by omega) hc
  rw [size_eq_sum, sum_fin_boundaries hn c] at hsize
  have hdecomp : (3 * n - 2) + ∑ i : Fin (3 * n - 2), (c ⟨i.val + 1, by omega⟩ - 1) =
      ∑ i : Fin (3 * n - 2), c ⟨i.val + 1, by omega⟩ := by
    calc
      _ = ∑ i : Fin (3 * n - 2),
          (1 + (c ⟨i.val + 1, by omega⟩ - 1)) := by
            simp [Finset.sum_add_distrib]
      _ = _ := by grind [Finset.sum_congr rfl]
  omega

theorem interior_excess_le_six (hn : 0 < n) {c : Hand n} (hc : IsFullWait c) :
    ∑ i : Fin (3 * n - 2), (c ⟨i.val + 1, by omega⟩ - 1) ≤ 6 := by
  have h := excess_eq_six hn hc
  omega

end Mahjong.Hand
