/-!
# Bitsets

Lean 4 does not yet have a built-in bitset type, so we implement a naive one here.
It is used to represent sets of states in dynamic programming algorithms.
For specifications and proofs of correctness, see `Spec` directory.
-/

class Bitset.Encoder (α : Type u) where
  size : Nat
  encode : α → Fin size

class Bitset.LawfulEncoder (α : Type u) [Bitset.Encoder α] : Prop where
  encode_injective : Function.Injective (Bitset.Encoder.encode (α := α))

structure Bitset (α : Type u) [Bitset.Encoder α] where
  bits : Nat
deriving BEq, Inhabited

namespace Bitset

instance : Encoder (Fin n) where
  size := n
  encode := id

def empty [Encoder α] : _root_.Bitset α :=
  ⟨0⟩

def singleton [Encoder α] (x : α) : _root_.Bitset α :=
  ⟨1 <<< (Encoder.encode x).val⟩

def mem [Encoder α] (s : _root_.Bitset α) (x : α) : Bool :=
  s.bits &&& (singleton x).bits != 0

def insert [Encoder α] (x : α) (s : _root_.Bitset α) : _root_.Bitset α :=
  ⟨s.bits ||| (singleton x).bits⟩

def union [Encoder α] (s t : _root_.Bitset α) : _root_.Bitset α :=
  ⟨s.bits ||| t.bits⟩

def inter [Encoder α] (s t : _root_.Bitset α) : _root_.Bitset α :=
  ⟨s.bits &&& t.bits⟩

def isEmpty [Encoder α] (s : _root_.Bitset α) : Bool :=
  s.bits == 0

def nonempty [Encoder α] (s : _root_.Bitset α) : Bool :=
  s.bits != 0

end Bitset
