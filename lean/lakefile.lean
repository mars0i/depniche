import Lake
open Lake DSL

package «depniche» where
  -- add package configuration options here

lean_lib «Depniche» where
  require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_exe «depniche» where
  root := `Main

