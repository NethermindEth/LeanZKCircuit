import LeanZKCircuit.Plonky3.Command.Air.Syntax.air_definition
import LeanZKCircuit.Plonky3.Command.util

open Lean Parser

namespace Plonky3
def append_air_structure_fields (base_string: String) (circuit: AirDefinition) : String :=
  circuit.entries.foldl (
    λ struct_string entry => match entry with
      | .column name => s!"{struct_string}\n  {name} (row : ℕ) (rotation : ℕ) : F"
      | .main_subair name typeName _ => s!"{struct_string}\n  {name} : Raw_{typeName} F"
      | .preprocessed_subair name typeName _ => s!"{struct_string}\n  {name} : Raw_{typeName} F"
  ) base_string

def append_subair_structure_fields (base_string: String) (circuit: SubAirDefinition) : String :=
  circuit.entries.foldl (
    λ struct_string entry => match entry with
      | .column name => s!"{struct_string}\n  {name} (row : ℕ) (rotation : ℕ) : F"
      | .subair name typeName _ => s!"{struct_string}\n  {name} : Raw_{typeName} F"
  ) base_string

def define_raw_air_structure
  (air_definition: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let base_structure_string : String :=
    s!"structure Raw_{air_definition.name} (F: Type) (ExtF : Type) where\n" ++
      "  bus : List (F × List F)\n" ++
      "  challenge (index: ℕ) : ExtF\n" ++
      "  main (column: ℕ) (row: ℕ) (rotation: ℕ) : F\n" ++
      "  permutation (column: ℕ) (row: ℕ) (rotation: ℕ) : ExtF\n" ++
      "  preprocessed (column: ℕ) (row: ℕ) (rotation: ℕ) : F\n" ++
      "  public_values (index: ℕ) : F\n" ++
      "  last_row: ℕ"

  let full_structure_string := append_air_structure_fields base_structure_string air_definition
  runAsCommand full_structure_string log

def define_raw_subair_structure
  (subair_definition: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let base_structure_string : String :=
    s!"structure Raw_{subair_definition.name} (F: Type) where\n" ++
      "  columns (column: ℕ) (row: ℕ) (rotation: ℕ) : F"

  let full_structure_string := append_subair_structure_fields base_structure_string subair_definition
  runAsCommand full_structure_string log
end Plonky3
