import Lake
open Lake DSL

package «variability» where
  -- add package configuration options here

@[default_target]
lean_lib «Variability» where
  -- add library configuration options here
  roots := #[`Var]

--@[default_target]
--lean_lib «variability» where
--  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"
