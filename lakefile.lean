import Lake

open System Lake DSL

package LeanZKCircuit where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.23.0-rc2"

@[default_target]
lean_lib LeanZKCircuit
