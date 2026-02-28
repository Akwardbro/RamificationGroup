import Lake
open Lake DSL

package «RamificationGroup» where
    leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «RamificationGroup» where
  -- add library configuration options here


require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

-- require local_class_field_theory from git "https://github.com/mariainesdff/LocalClassFieldTheory.git"

-- meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
-- require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.13.0"
