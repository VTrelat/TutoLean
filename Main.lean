import Tuto.Extra
open Lst Chr

def main : IO Unit := do
  let s₁ : Str := #⟦72, 101, 108, 108, 111, 44, 32⟧
  let s₂ : Lst Chr := ⟦67, 108, 101, 97, 114, 115, 121⟧

  have : s₁.size = s₂.size := rfl
  if s₁.size = s₂.size then
    println! s₁ ++ s₂.toVec
