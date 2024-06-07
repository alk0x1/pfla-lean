import Lake
open Lake DSL

package «plfa» where
  -- add package configuration options here

lean_lib «Plfa» where
  -- add library configuration options here

@[default_target]
lean_exe «plfa» where
  root := `Main
