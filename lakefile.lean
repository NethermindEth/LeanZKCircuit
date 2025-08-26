import Lake

open System Lake DSL

package LeanZKCircuit where version := v!"0.1.0"

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib LeanZKCircuit
