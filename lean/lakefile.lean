import Lake
open Lake DSL

package «depniche» where
  -- add package configuration options here

lean_lib «Depniche» where
  require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «depniche» where
  root := `Main

