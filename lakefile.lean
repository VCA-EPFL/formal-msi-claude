import Lake
open Lake DSL

package «formal-msi» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"

@[default_target]
lean_lib «FormalMSI» where
  -- add library configuration options here

--lean_exe «formal-msi» where
--  root := `Main
