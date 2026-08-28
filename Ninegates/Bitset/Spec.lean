import Ninegates.Bitset.Basic
import Init.Grind.Tactics

/-!
# Bitset specifications

The lemmas in this file describe the operations used by the dynamic-programming algorithms.
They are deliberately stated as executable Boolean equations, so later correctness proofs can
rewrite state-set operations without exposing the underlying bit mask.
-/

namespace Bitset

variable {α : Type u} [Encoder α]

private theorem and_pow_eq_zero_iff (a k : Nat) :
    a &&& 2 ^ k = 0 ↔ a.testBit k = false := by
  constructor
  · intro h
    have h' := congrArg (fun x : Nat => x.testBit k) h
    simpa using h'
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hik : i = k
    · simp [hik, h]
    · have hki : k ≠ i := Ne.symm hik
      simp [hki]

private theorem and_pow_bne_zero (a k : Nat) :
    (a &&& 2 ^ k != 0) = a.testBit k := by
  cases h : a.testBit k with
  | false =>
      have hz : a &&& 2 ^ k = 0 := (and_pow_eq_zero_iff a k).2 h
      simp [hz]
  | true =>
      have hnz : a &&& 2 ^ k ≠ 0 := by
        intro hz
        have := (and_pow_eq_zero_iff a k).1 hz
        simp [h] at this
      simp [bne_eq, hnz]

theorem mem_eq_testBit (s : _root_.Bitset α) (x : α) :
    mem s x = s.bits.testBit (Encoder.encode x).val := by
  simp only [mem, singleton, Nat.one_shiftLeft]
  exact and_pow_bne_zero _ _

@[simp, grind =]
theorem mem_singleton_encode (x y : α) :
    mem (singleton x) y = decide (Encoder.encode x = Encoder.encode y) := by
  simp [mem_eq_testBit, singleton, Nat.one_shiftLeft, Nat.testBit_two_pow, Fin.ext_iff]

@[simp, grind =]
theorem mem_singleton [LawfulEncoder α] [DecidableEq α] (x y : α) :
    mem (singleton x) y = decide (x = y) := by
  by_cases h : x = y
  · simp [mem_singleton_encode, h]
  · have h' : Encoder.encode x ≠ Encoder.encode y :=
      fun heq => h (LawfulEncoder.encode_injective heq)
    simp [mem_singleton_encode, h, h']

@[simp, grind =]
theorem mem_singleton_iff [LawfulEncoder α] (x y : α) :
    mem (singleton x) y = true ↔ x = y := by
  simp only [mem_singleton_encode, decide_eq_true_eq]
  exact ⟨fun h => LawfulEncoder.encode_injective h, congrArg _⟩

@[simp, grind =]
theorem mem_empty (x : α) : mem (empty : _root_.Bitset α) x = false := by
  simp [mem, empty, singleton]

@[simp, grind =]
theorem mem_insert (x y : α) (s : _root_.Bitset α) :
    mem (insert x s) y = (mem s y || mem (singleton x) y) := by
  simp [mem_eq_testBit, insert, Nat.testBit_or]

@[simp, grind =]
theorem mem_union (s t : _root_.Bitset α) (x : α) :
    mem (union s t) x = (mem s x || mem t x) := by
  simp [mem_eq_testBit, union, Nat.testBit_or]

@[simp, grind =]
theorem mem_inter (s t : _root_.Bitset α) (x : α) :
    mem (inter s t) x = (mem s x && mem t x) := by
  simp [mem_eq_testBit, inter, Nat.testBit_and]

@[simp, grind =]
theorem mem_insert_iff [LawfulEncoder α] (x y : α) (s : _root_.Bitset α) :
    mem (insert x s) y = true ↔ mem s y = true ∨ x = y := by
  simp only [mem_insert, Bool.or_eq_true, mem_singleton_iff]

@[simp, grind =]
theorem mem_union_iff (s t : _root_.Bitset α) (x : α) :
    mem (union s t) x = true ↔ mem s x = true ∨ mem t x = true := by
  simp only [mem_union, Bool.or_eq_true]

@[simp, grind =]
theorem mem_inter_iff (s t : _root_.Bitset α) (x : α) :
    mem (inter s t) x = true ↔ mem s x = true ∧ mem t x = true := by
  simp only [mem_inter, Bool.and_eq_true]

@[simp, grind =]
theorem nonempty_empty : nonempty (empty : _root_.Bitset α) = false := by
  simp [nonempty, empty]

@[simp, grind =]
theorem nonempty_singleton (x : α) : nonempty (singleton x) = true := by
  simp [nonempty, singleton, Nat.one_shiftLeft]

@[grind →]
theorem nonempty_of_mem {s : _root_.Bitset α} {x : α}
    (h : mem s x = true) : nonempty s = true := by
  by_cases hs : s.bits = 0
  · simp [mem, hs, singleton] at h
  · simp [nonempty, hs]

@[grind →]
theorem nonempty_inter_of_mem {s t : _root_.Bitset α} {x : α}
    (hs : mem s x = true) (ht : mem t x = true) :
    nonempty (inter s t) = true := by
  apply nonempty_of_mem
  simp only [mem_inter, Bool.and_eq_true]
  exact ⟨hs, ht⟩

end Bitset
