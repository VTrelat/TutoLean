import Tuto.Extra
open Lst Chr

/--
`alternate u v h` takes two lists `u` and `v` of the same length, given
by `h`, and returns a list containing the elements of `u` and `v` alternatingly.
-/
def alternate {α} (u v : Lst α) (h : u.size = v.size) : Lst α :=
  match u, v, h with
  | nil, v, h => nil
  | u, nil, h => u
  | cons x xs, cons y ys, h =>
    have h' : xs.size = ys.size := by injection h
    cons x (cons y (alternate xs ys h'))

def main : IO Unit := do
  let s₁ : Str := #⟦72, 101, 108, 108, 111, 44, 32⟧
  let s₂ : Lst Chr := ⟦67, 108, 101, 97, 114, 115, 121⟧

  -- have : s₁.size = s₂.size := rfl
  if s₁.size = s₂.size then
    println! s₁ ++ s₂.toVec
    let s₃ := (alternate s₂ s₁.toLst rfl |>.toVec)
    println! "{s₃} has size {s₃.size}"
