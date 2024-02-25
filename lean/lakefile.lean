import Lake
open Lake DSL

package «depniche» where
  -- add package configuration options here

lean_lib «Depniche» where
  -- add library configuration options here

@[default_target]
lean_exe «depniche» where
  root := `Main
