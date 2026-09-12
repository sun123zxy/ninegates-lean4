module

public import Ninegates.Standard.Defs
public import Ninegates.Operations.Basic
public import Ninegates.Wait.Basic

/-!
# Insertion within the eight standard families

Coordinate formulas and insertion lemmas for the standard families, culminating in
`IsEightFamily.insertSeqAt`. These proofs use no computational certificates.
-/

@[expose] public section

namespace Mahjong.Hand

variable {n : ℕ}

namespace Standard

@[grind =]
lemma A.apply (n : ℕ) (i : Fin (3 * n)) :
    A n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 3 else 1 := by rfl

@[grind =]
lemma B.apply (n : ℕ) (i : Fin (3 * n)) :
    B n i = if i.val = 0 then 3 else if i.val = 3 * n - 4 then 4
    else if i.val = 3 * n - 1 then 0 else 1 := rfl

@[simp]
lemma B'.eq_reverse (n : ℕ) : B' n = reverse (B n) := rfl

@[grind =]
lemma B'.apply (n : ℕ) (i : Fin (3 * n)) :
    B' n i = if i.val = 3 * n - 1 then 3 else if i.val = 3 then 4
      else if i.val = 0 then 0 else 1 := by
  simp only [B', reverse_apply, B.apply, Fin.rev]
  grind

@[grind =]
lemma C.apply (n : ℕ) (i : Fin (3 * n)) :
    C n i = if i.val = 2 then 4 else if i.val = 3 * n - 2 then 3
    else if i.val = 3 * n - 1 then 0 else 1 := rfl

@[simp]
lemma C'.eq_reverse (n : ℕ) : C' n = reverse (C n) := rfl

@[grind =]
lemma C'.apply (n : ℕ) (i : Fin (3 * n)) :
    C' n i = if i.val = 3 * n - 3 then 4 else if i.val = 1 then 3
      else if i.val = 0 then 0 else 1 := by
  simp only [C', reverse_apply, C.apply, Fin.rev]
  grind

@[grind =]
lemma D.apply (n : ℕ) (i : Fin (3 * n)) :
    D n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 0 else if i.val = 2 then 4
    else if i.val = 3 then 2 else if i.val = 3 * n - 2 then 3 else 1 := rfl

@[simp]
lemma D'.eq_reverse (n : ℕ) : D' n = reverse (D n) := rfl

@[grind =]
lemma D'.apply (n : ℕ) (i : Fin (3 * n)) :
    D' n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 0
      else if i.val = 3 * n - 3 then 4 else if i.val = 3 * n - 4 then 2
      else if i.val = 1 then 3 else 1 := by
  simp only [D', reverse_apply, D.apply, Fin.rev]
  grind

@[grind =]
lemma E.apply (n : ℕ) (i : Fin (3 * n)) :
    E n i = if i.val = 0 ∨ i.val = 3 * n - 1 then 0
    else if (n = 2 ∧ (i.val = 2 ∨ i.val = 3)) ∨
      (n ≠ 2 ∧ (i.val = 3 ∨ i.val = 3 * n - 4)) then 4 else 1 := rfl

/-! ## Insertion within the eight families -/

lemma A.insertSeqAt (k : Fin (3 * n)) (hk : 0 < k.val) :
    (A n).insertSeqAt k = A (n + 1) := by
  ext i
  grind

lemma B.insertSeqAt (hn : 2 ≤ n) (k : Fin (3 * n))
    (hk₀ : 1 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 4) :
    (B n).insertSeqAt k = B (n + 1) := by
  ext i
  grind (splits := 20)

lemma B'.insertSeqAt (hn : 2 ≤ n) (k : Fin (3 * n))
    (hk₀ : 4 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 1) :
    (B' n).insertSeqAt k = B' (n + 1) := by
  ext i
  grind (splits := 20)

lemma C.insertSeqAt (hn : 2 ≤ n) (k : Fin (3 * n))
    (hk₀ : 3 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 2) :
    (C n).insertSeqAt k = C (n + 1) := by
  ext i
  grind (splits := 20)

lemma C'.insertSeqAt (hn : 2 ≤ n) (k : Fin (3 * n))
    (hk₀ : 2 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 3) :
    (C' n).insertSeqAt k = C' (n + 1) := by
  ext i
  grind (splits := 20)

lemma D.insertSeqAt (hn : 2 ≤ n) (k : Fin (3 * n))
    (hk₀ : 4 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 2) :
    (D n).insertSeqAt k = D (n + 1) := by
  ext i
  grind (splits := 20)

lemma D'.insertSeqAt (hn : 2 ≤ n) (k : Fin (3 * n))
    (hk₀ : 2 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 4) :
    (D' n).insertSeqAt k = D' (n + 1) := by
  ext i
  grind (splits := 20)

lemma E.insertSeqAt (hn : 3 ≤ n) (k : Fin (3 * n))
    (hk₀ : 4 ≤ k.val) (hk₁ : k.val ≤ 3 * n - 4) :
    (E n).insertSeqAt k = E (n + 1) := by
  ext i
  grind (splits := 20)

/-- Drawing the second rank rules out an initial `111`. -/
private lemma not_isFullWait_of_prefix_111 (hn : 0 < n) {c : Hand n}
    (hc : IsFullWait c) (h₀ : c ⟨0, by omega⟩ = 1)
    (h₁ : c ⟨1, by omega⟩ = 1) (h₂ : c ⟨2, by omega⟩ = 1) : False := by
  obtain ⟨_, d, p, ⟨q, hq⟩, heq⟩ := hc ⟨1, by omega⟩
  have h0 := congrArg (fun w : Hand n ↦ w ⟨0, by omega⟩) heq
  have h1 := congrArg (fun w : Hand n ↦ w ⟨1, by omega⟩) heq
  have h2 := congrArg (fun w : Hand n ↦ w ⟨2, by omega⟩) heq
  grind [Meldable.IsWitness]

/-- Drawing the third rank rules out initial `0111` and `0141`. -/
private lemma not_isFullWait_of_prefix_01x1 (hn : 2 ≤ n) {c : Hand n}
    (hc : IsFullWait c) (h₀ : c ⟨0, by omega⟩ = 0)
    (h₁ : c ⟨1, by omega⟩ = 1)
    (h₂ : c ⟨2, by omega⟩ = 1 ∨ c ⟨2, by omega⟩ = 4)
    (h₃ : c ⟨3, by omega⟩ = 1) : False := by
  obtain ⟨_, d, p, ⟨q, hq⟩, heq⟩ := hc ⟨2, by omega⟩
  have h0 := congrArg (fun w : Hand n ↦ w ⟨0, by omega⟩) heq
  have h1 := congrArg (fun w : Hand n ↦ w ⟨1, by omega⟩) heq
  have h2 := congrArg (fun w : Hand n ↦ w ⟨2, by omega⟩) heq
  have h3 := congrArg (fun w : Hand n ↦ w ⟨3, by omega⟩) heq
  grind [Meldable.IsWitness]

lemma A.insertSeqAt_pos (k : Fin (3 * n))
    (hc : IsFullWait ((A n).insertSeqAt k)) : 0 < k.val := by
  by_contra hk
  apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind

lemma B.insertSeqAt_bounds (hn : 2 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((B n).insertSeqAt k)) :
    1 ≤ k.val ∧ k.val ≤ 3 * n - 4 := by
  constructor
  · by_contra hk
    apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
  · by_contra hk
    apply not_isFullWait_of_prefix_01x1 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind (splits := 20)

lemma B'.insertSeqAt_bounds (hn : 2 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((B' n).insertSeqAt k)) :
    4 ≤ k.val ∧ k.val ≤ 3 * n - 1 := by
  constructor
  · by_contra hk
    by_cases hk₀ : k.val = 0
    · apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
    · apply not_isFullWait_of_prefix_01x1 (by omega) hc <;> grind (splits := 20)
  · omega

lemma C.insertSeqAt_bounds (hn : 2 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((C n).insertSeqAt k)) :
    3 ≤ k.val ∧ k.val ≤ 3 * n - 2 := by
  constructor
  · by_contra hk
    apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
  · by_contra hk
    apply not_isFullWait_of_prefix_01x1 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind (splits := 20)

lemma C'.insertSeqAt_bounds (hn : 2 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((C' n).insertSeqAt k)) :
    2 ≤ k.val ∧ k.val ≤ 3 * n - 3 := by
  constructor
  · by_contra hk
    by_cases hk₀ : k.val = 0
    · apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
    · apply not_isFullWait_of_prefix_01x1 (by omega) hc <;> grind (splits := 20)
  · by_contra hk
    apply not_isFullWait_of_prefix_111 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind (splits := 20)

lemma D.insertSeqAt_bounds (hn : 2 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((D n).insertSeqAt k)) :
    4 ≤ k.val ∧ k.val ≤ 3 * n - 2 := by
  constructor
  · by_contra hk
    by_cases hk₀ : k.val = 0
    · apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
    · apply not_isFullWait_of_prefix_01x1 (by omega) hc <;> grind (splits := 20)
  · by_contra hk
    apply not_isFullWait_of_prefix_01x1 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind (splits := 20)

lemma D'.insertSeqAt_bounds (hn : 2 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((D' n).insertSeqAt k)) :
    2 ≤ k.val ∧ k.val ≤ 3 * n - 4 := by
  constructor
  · by_contra hk
    by_cases hk₀ : k.val = 0
    · apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
    · apply not_isFullWait_of_prefix_01x1 (by omega) hc <;> grind (splits := 20)
  · by_contra hk
    apply not_isFullWait_of_prefix_01x1 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind (splits := 20)

lemma E.insertSeqAt_bounds (hn : 3 ≤ n) (k : Fin (3 * n))
    (hc : IsFullWait ((E n).insertSeqAt k)) :
    4 ≤ k.val ∧ k.val ≤ 3 * n - 4 := by
  constructor
  · by_contra hk
    by_cases hk₀ : k.val = 0
    · apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
    · apply not_isFullWait_of_prefix_01x1 (by omega) hc <;> grind (splits := 20)
  · by_contra hk
    apply not_isFullWait_of_prefix_01x1 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind (splits := 20)

lemma E.not_isFullWait_insertSeqAt_two (k : Fin (3 * 2)) :
    ¬ IsFullWait ((E 2).insertSeqAt k) := by
  intro hc
  by_cases hk₀ : k.val = 0
  · apply not_isFullWait_of_prefix_111 (by omega) hc <;> grind
  by_cases hk₁ : k.val < 4
  · apply not_isFullWait_of_prefix_01x1 (by omega) hc <;> grind
  · apply not_isFullWait_of_prefix_01x1 (by omega) hc.reverse <;>
      simp only [reverse_apply, Fin.rev] <;> grind

end Standard

/-- Inserting `111` into an eight-family hand, if it remains a full wait,
gives an eight-family hand of the next order. -/
theorem IsEightFamily.insertSeqAt (hn : 2 ≤ n) {c : Hand n}
    (hc : IsEightFamily c) (k : Fin (3 * n)) (hfull : IsFullWait (c.insertSeqAt k)) :
    IsEightFamily (c.insertSeqAt k) := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Standard.A.insertSeqAt k (Standard.A.insertSeqAt_pos k hfull)]
    simp [IsEightFamily]
  · obtain ⟨hk₀, hk₁⟩ := Standard.B.insertSeqAt_bounds hn k hfull
    simp only [Standard.B.insertSeqAt hn k hk₀ hk₁]
    simp [IsEightFamily]
  · obtain ⟨hk₀, hk₁⟩ := Standard.B'.insertSeqAt_bounds hn k hfull
    simp only [Standard.B'.insertSeqAt hn k hk₀ hk₁]
    simp [IsEightFamily]
  · obtain ⟨hk₀, hk₁⟩ := Standard.C.insertSeqAt_bounds hn k hfull
    simp only [Standard.C.insertSeqAt hn k hk₀ hk₁]
    simp [IsEightFamily]
  · obtain ⟨hk₀, hk₁⟩ := Standard.C'.insertSeqAt_bounds hn k hfull
    simp only [Standard.C'.insertSeqAt hn k hk₀ hk₁]
    simp [IsEightFamily]
  · obtain ⟨hk₀, hk₁⟩ := Standard.D.insertSeqAt_bounds hn k hfull
    simp only [Standard.D.insertSeqAt hn k hk₀ hk₁]
    simp [IsEightFamily]
  · obtain ⟨hk₀, hk₁⟩ := Standard.D'.insertSeqAt_bounds hn k hfull
    simp only [Standard.D'.insertSeqAt hn k hk₀ hk₁]
    simp [IsEightFamily]
  · by_cases hn₂ : n = 2
    · subst n
      exact (Standard.E.not_isFullWait_insertSeqAt_two k hfull).elim
    have hn₃ : 3 ≤ n := by omega
    obtain ⟨hk₀, hk₁⟩ := Standard.E.insertSeqAt_bounds hn₃ k hfull
    simp only [Standard.E.insertSeqAt hn₃ k hk₀ hk₁]
    simp [IsEightFamily]

end Mahjong.Hand
