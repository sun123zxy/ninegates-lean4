import NinegatesFormalization.Basic

namespace Mahjong.Hand

namespace Meldable

section Basics

structure StepPlacement where
  tripNum : ℕ
  seqNum : ℕ
deriving DecidableEq, Repr

abbrev ScanState := ℕ × ℕ -- i-1, i-2

inductive ScanFailure where
  | failEarly
  | failFinally

abbrev ScanM := StateT ScanState (WriterT (List StepPlacement) (Except ScanFailure))

def scanStep (x : ℕ) : ScanM Unit := do
  let s ← get
  unless s.1 + s.2 ≤ x do throw .failEarly
  let rem := x - (s.1 + s.2)
  let p : StepPlacement := ⟨rem / 3, rem % 3⟩
  tell [p]
  set (p.seqNum, s.1)

def scanList (xs : List ℕ) : ScanM Unit := do
  xs.forM scanStep
  unless (← get) = (0, 0) do throw .failFinally

variable {n : ℕ}

def scanHand (c : Hand n) := scanList (List.ofFn c) (0, 0)

end Basics

theorem iff_scan (c : Hand n) : Meldable c ↔ (scanHand c).isOk := by
  sorry

end Meldable

end Mahjong.Hand
