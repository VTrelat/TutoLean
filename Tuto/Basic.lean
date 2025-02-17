import Mathlib.Data.Set.Defs

inductive Lst (α : Type) where
  | nil : Lst α
  | cons : α → Lst α → Lst α
  deriving Inhabited

namespace Lst
variable {α : Type}

def concat : Lst α → α → Lst α
  | nil, a => cons a nil
  | cons x v, a => cons x (concat v a)

@[simp]
def append : Lst α → Lst α → Lst α
  | nil, v => v
  | cons x u, v => cons x (append u v)

@[reducible] instance : HAppend (Lst α) (Lst α) (Lst α) := ⟨Lst.append⟩

@[simp]
def rev : Lst α → Lst α
  | nil => nil
  | cons a v => concat (Lst.rev v) a

def size : Lst α → Nat
  | nil => 0
  | cons _ v => size v + 1

def toSet {α : Type} : Lst α → Set α
  | nil => {}
  | cons x xs => {x} ∪ xs.toSet

end Lst

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n+1)

namespace Vec

def size {α : Type} {n : Nat} (_ : Vec α n) : Nat := n

def toLst {α : Type} {n : Nat} (v : Vec α n) : Lst α :=
  match v with
  | .nil => .nil
  | .cons a v => .cons a (toLst v)

def ofLst {α : Type} : (l : Lst α) → Vec α l.size
  | .nil => Vec.nil
  | .cons a v =>
    let eq : v.size + 1 = (v.cons a).size := by rw [Lst.size, Nat.add_comm]
    eq ▸ Vec.cons a (ofLst v)

def append {α : Type} {n m : Nat} (v : Vec α n) (w : Vec α m) : Vec α (m+n) :=
  match v with
  | .nil => w
  | .cons a u => Vec.cons a (append u w)

def toSet {α : Type} {n : Nat} : Vec α n → Set α
  | nil => {}
  | cons x xs => {x} ∪ xs.toSet

end Vec

abbrev Lst.toVec {α} (l : Lst α) := Vec.ofLst l

abbrev Chr := { x : Nat // x < 256 }
abbrev Str {n : Nat} := Vec Chr n
