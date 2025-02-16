import Tuto.Extra
open Lst Chr

def main : IO UInt32 := do
  let s₁ : Str := #⟦72, 101, 108, 108, 111, 44, 32⟧
  let s₂ : Str := #⟦67, 108, 101, 97, 114, 115, 121⟧

  have sanityCheck : s₁.size = s₂.size := rfl

  if sanityCheck : s₁.size = s₂.size then
    println! s₁ ++ s₂
    return 0
  else
    return 1
