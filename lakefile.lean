import Lake
open Lake DSL

package "concrete-semantics-lean" where
  version := v!"0.1.0"

lean_lib «ConcreteSemanticsLean» where
  -- add library configuration options here

@[default_target]
lean_exe "concrete-semantics-lean" where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
