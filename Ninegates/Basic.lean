/-
Copyright (c) 2026 Xingyu Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingyu Zhong
-/
module

public import Ninegates.Defs

/-!
# Basic properties of Mahjong hands

Definitions and instances are in `Ninegates.Defs`.

## Design notes

### Comparison convention of `Fin`

When comparing `i j : Fin (3 * n)`, we tend to retreat to `Nat` by `Fin.val`.
That is, write `i.val < j.val` instead of `i < j`, or `i.val = j.val` instead of `i = j`.
This helps us to maintain a canonical writing and a smooth proof automation,
as comparison on `Fin` is defined in terms of the underlying `Nat` comparison anyway.

### Hide of `∑`

As a general policy in this library, if a definition mentions `∑`,
we shall hide it from the downstream, as `∑` often breaks proof automation.

Thus we refrain from annotate `Hand`'s defining lemma with `@[grind]` or `@[simp]`.
We provide `grind`/`simp`-annotated lemmas free of `∑` for downstream use,
and non-`grind`/`simp`-annotated `xxx_eq_sum` lemmas for the rare occasions when `∑` is needed.
-/

@[expose] public section

namespace Mahjong

namespace Hand

variable {n : ℕ}

@[simp, grind =]
lemma mk_apply (count : Fin (3 * n) → ℕ) (i : Fin (3 * n)) :
    (⟨count⟩ : Hand n) i = count i := rfl

lemma size_eq_sum (c : Hand n) : size c = ∑ i, c i := rfl

lemma sum_eq_sum (c : Hand n) : sum c = ∑ i, i.val * c i := rfl

/-- Split a sum over tile ranks into its two boundaries and its interior. -/
lemma sum_fin_boundaries {n : Nat} (hn : 1 ≤ n) (f : Fin (3 * n) → Nat) :
    (∑ i : Fin (3 * n), f i) =
      f ⟨0, by omega⟩ +
        (∑ i : Fin (3 * n - 2), f ⟨i.val + 1, by omega⟩) +
      f ⟨3 * n - 1, by omega⟩ := by
  have hsumFin (g : Fin ((3 * n - 2) + 2) → Nat) :
      (∑ i, g i) =
        g 0 + (∑ i : Fin (3 * n - 2), g i.castSucc.succ) +
          g (Fin.last (3 * n - 2 + 1)) := by
    grind [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  let e : Fin ((3 * n - 2) + 2) ≃ Fin (3 * n) := finCongr (by omega)
  have he0 : e 0 = ⟨0, by omega⟩ := by simp [Fin.ext_iff, e]
  have heMid (i : Fin (3 * n - 2)) :
      e i.castSucc.succ = ⟨i.val + 1, by omega⟩ := by
    simp [Fin.ext_iff, e]
  have heLast :
      e (Fin.last (3 * n - 2 + 1)) = ⟨3 * n - 1, by omega⟩ := by
    simp [Fin.ext_iff, e]
    omega
  grind [Equiv.sum_comp e f]

@[simp, grind =]
lemma single_apply (i j : Fin (3 * n)) :
    single i j = if j.val = i.val then 1 else 0 := by
  grind [single]

@[simp, grind =]
lemma size_single (i : Fin (3 * n)) : size (single i) = 1 := by
  simp [size, single]

@[simp, grind =]
lemma sum_single (i : Fin (3 * n)) : sum (single i) = i.val := by
  simp [sum, single]

@[simp, grind =]
lemma pair_apply (i j : Fin (3 * n)) :
    pair i j = if j.val = i.val then 2 else 0 := by simp [pair]

@[simp, grind =]
lemma size_pair (i : Fin (3 * n)) : size (pair i) = 2 := by simp [pair]

@[simp, grind =]
lemma sum_pair (i : Fin (3 * n)) : sum (pair i) = 2 * i.val := by simp [pair]

@[simp, grind =]
lemma triplet_apply (i j : Fin (3 * n)) :
    triplet i j = if j.val = i.val then 3 else 0 := by grind [triplet]

@[simp, grind =]
lemma size_triplet (i : Fin (3 * n)) : size (triplet i) = 3 := by simp [triplet]

@[simp, grind =]
lemma sum_triplet (i : Fin (3 * n)) : sum (triplet i) = 3 * i.val := by simp [triplet]

@[simp, grind =]
lemma sequence_apply (i : Fin (3 * n - 2)) (j : Fin (3 * n)) :
    sequence i j = if j.val = i.val ∨ j.val = i.val + 1 ∨ j.val = i.val + 2 then 1 else 0 := by
  grind [sequence]

@[simp, grind =]
lemma size_sequence (i : Fin (3 * n - 2)) : size (sequence i) = 3 := by
  grind [sequence]

@[simp, grind =]
lemma sum_sequence (i : Fin (3 * n - 2)) : sum (sequence i) = 3 * (i.val + 1) := by
  grind [sequence]

@[simp, grind =]
lemma reverse_apply (c : Hand n) (i : Fin (3 * n)) : reverse c i = c i.rev := rfl

@[simp]
lemma reverse_reverse (c : Hand n) : reverse (reverse c) = c := by ext; simp

@[simp]
lemma size_reverse (c : Hand n) : size (reverse c) = size c := by
  let e : Fin (3 * n) ≃ Fin (3 * n) := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  exact Equiv.sum_comp e c

@[simp]
lemma reverse_single (i : Fin (3 * n)) : reverse (single i) = single i.rev := by
  ext j
  simp only [reverse_apply, single_apply, Fin.rev]
  grind

@[simp]
lemma reverse_pair (i : Fin (3 * n)) : reverse (pair i) = pair i.rev := by
  simp [pair]

@[simp]
lemma reverse_triplet (i : Fin (3 * n)) : reverse (triplet i) = triplet i.rev := by
  simp [triplet]

@[simp]
lemma reverse_sequence (i : Fin (3 * n - 2)) : reverse (sequence i) = sequence i.rev := by
  ext j
  simp only [reverse_apply, sequence_apply, Fin.rev]
  grind

end Hand

end Mahjong
