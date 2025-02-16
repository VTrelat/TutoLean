import Lake
open Lake DSL

package «Tuto» where
  -- add package configuration options here
  leanOptions := #[
    -- ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]

lean_lib «Tuto» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"v{Lean.versionString}"

@[default_target]
lean_exe «tuto» where
  root := `Main
