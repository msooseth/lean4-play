import Lake
open Lake DSL

package "numerals" where
  -- add package configuration options here

lean_lib «Numerals» where
  -- add library configuration options here

@[default_target]
lean_exe "numerals" where
  root := `Main
