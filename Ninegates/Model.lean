import Mathlib

namespace Ninegates

/-- A count vector stores the multiplicity of each of `n` ranks. -/
def Counts (n : ℕ) := Fin n → ℕ

/-- The count vector containing one tile at `i` and no tiles elsewhere. -/
def basis {n : ℕ} (i : Fin n) : Counts n :=
  fun j ↦ if j = i then 1 else 0

/-- The total number of tiles represented by a count vector. -/
def total {n : ℕ} (c : Counts n) : ℕ :=
  ∑ i, c i

/-- Remove two tiles at `p`, using truncated subtraction on natural counts. -/
def removePair {n : ℕ} (c : Counts n) (p : Fin n) : Counts n :=
  fun i ↦ c i - 2 * basis p i

/--
A count vector is meldable when it is a sum of rank triplets and
three-consecutive-rank runs. Run starts are indexed by `Fin (m - 2)`, so a
run cannot extend past the right endpoint.
-/
def Meldable {m : ℕ} (d : Counts m) : Prop :=
  ∃ triplets : Counts m, ∃ runs : Fin (m - 2) → ℕ,
    ∀ i : Fin m,
      d i =
        3 * triplets i +
          ∑ j, if j.val ≤ i.val ∧ i.val ≤ j.val + 2 then runs j else 0

/-- A complete hand consists of one pair and a meldable remainder. -/
def Complete {n : ℕ} (w : Counts n) : Prop :=
  ∃ p : Fin n, 2 ≤ w p ∧ Meldable (removePair w p)

/--
A live all-rank wait has at most three tiles at every rank, has total
`n + 4`, and becomes complete after drawing any rank.
-/
def LiveWait {n : ℕ} (c : Counts n) : Prop :=
  (∀ i : Fin n, c i ≤ 3) ∧
    total c = n + 4 ∧
      ∀ x : Fin n, Complete (fun i ↦ c i + basis x i)

/--
The standard count vector has multiplicity three at each endpoint and one
at every internal rank.
-/
def standard (n : ℕ) : Counts n :=
  fun i ↦ if i.val = 0 ∨ i.val + 1 = n then 3 else 1

end Ninegates
