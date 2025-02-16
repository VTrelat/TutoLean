import Tuto.Basic

namespace Lst

def intersperse {α} (sep : α) : Lst α → Lst α
  | nil => nil
  | cons a .nil => cons a nil
  | cons a v => cons a (cons sep (intersperse sep v))

def aux {α} [Repr α] : Lst α → Lst Std.Format
  | nil => nil
  | cons a v => cons (repr a) (aux v)

def join : Lst Std.Format → Std.Format
  | nil => .nil
  | cons a v => a ++ join v

def repr {α} [Repr α] (v : Lst α) (_ : Nat) : Std.Format :=
  .bracket "⟦" (v.aux.intersperse ↑", ").join "⟧"

instance {α} [Repr α] : Repr (Lst α) := ⟨repr⟩

@[simp]
def mem {α} : Lst α → α → Prop
  | nil, _ => False
  | cons y xs, x => x = y ∨ mem xs x

@[reducible] instance {α} : Membership α (Lst α) := ⟨mem⟩
end Lst

namespace Vec

@[push_cast]
theorem cast_cons {α} {n m : Nat} (h : n = m) (x : α) (v : Vec α n) : h ▸ v.cons x = (h ▸ v).cons x := by
  cases h
  rfl

@[simp]
theorem cast_symm {α} {n m} (h : n = m) (v : Vec α n) : h ▸ h.symm ▸ v = v := by
  cases h
  rfl

@[reducible]
instance {α} [Repr α] {n : Nat} : Repr (Vec α n) where
  reprPrec v _ := Lst.repr v.toLst 0

instance {α : Type} {n m : Nat} : HAppend (Vec α n) (Vec α m) (Vec α (m+n)) := ⟨append⟩

@[simp]
def mem {α n} : Vec α n → α → Prop
  | nil, _ => False
  | cons y xs, x => y = x ∨ mem xs x

@[reducible] instance {α n} : Membership α (Vec α n) := ⟨mem⟩

end Vec

namespace Chr

instance {n : Nat} : OfNat Chr n where
  ofNat := ⟨n % 256, Nat.mod_lt _ (Nat.zero_lt_succ 255)⟩

instance : Repr Chr where
  reprPrec c _ := Char.toString <| Char.ofUInt8 <| UInt8.ofNat c.val

end Chr

namespace Str

instance {n} : Repr <| @Str n where
  reprPrec s _ :=
    let rec go {n} : Vec Chr n → Std.Format
      | .nil => .nil
      | @Vec.cons _ n c v => repr c ++ go v
    go s

instance {n} : ToString (@Str n) where
  toString s := ToString.toString <| repr s

end Str

syntax "⟦" term,*,? "⟧" : term
macro_rules
  | `(term| ⟦⟧) => `(term| Lst.nil)
  | `(term| ⟦$x⟧) => `(term| Lst.cons $x Lst.nil)
  | `(term| ⟦$x, $xs,*⟧) => `(term| Lst.cons $x ⟦$xs,*⟧)

syntax "#⟦" term,*,? "⟧" : term
macro_rules
  | `(term| #⟦⟧) => `(term| Vec.nil)
  | `(term| #⟦$x⟧) => `(term| Vec.cons $x Vec.nil)
  | `(term| #⟦$x, $xs,*⟧) => `(term| Vec.cons $x #⟦$xs,*⟧)
