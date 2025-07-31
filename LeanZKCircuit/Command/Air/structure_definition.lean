import Mathlib

import LeanZKCircuit.Command.Air.Syntax.circuit_definition
import LeanZKCircuit.Command.util

open Lean Parser


def append_structure_fields (base_string: String) (circuit: CircuitDefinition) : String :=
  circuit.entries.foldl (
    λ struct_string entry => match entry with
      | .column name => s!"{struct_string}\n  {name} (row : ℕ) (rotation : ℕ) : F"
      | .subair name typeName _ => s!"{struct_string}\n  {name} : Raw_{typeName} F ExtF"
  ) base_string

def define_raw_air_structure
  (circuit_definition: CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let base_structure_string : String :=
    s!"structure Raw_{circuit_definition.name} (F: Type) (ExtF : Type) where\n" ++
      "  buses (index: ℕ) : List (F × List F)\n" ++
      "  challenge (index: ℕ) : ExtF\n" ++
      "  exposed (index: ℕ) : ExtF\n" ++ -- TODO should this be ExtF?
      "  main (id: ℕ) (column: ℕ) (row: ℕ) (rotation: ℕ) : F\n" ++
      "  permutation (column: ℕ) (row: ℕ) (rotation: ℕ) : ExtF\n" ++
      "  preprocessed (column: ℕ) (row: ℕ) (rotation: ℕ) : F\n" ++
      "  public_values (index: ℕ) : F\n" ++
      "  last_row: ℕ"

  let full_structure_string := append_structure_fields base_structure_string circuit_definition
  runAsCommand full_structure_string log
