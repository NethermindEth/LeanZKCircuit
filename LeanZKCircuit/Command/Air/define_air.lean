import Mathlib

import LeanZKCircuit.OpenVM.Circuit

import LeanZKCircuit.Command.Air.Syntax.circuit_definition
import LeanZKCircuit.Command.Air.assign_columns
import LeanZKCircuit.Command.Air.instance_creation
import LeanZKCircuit.Command.Air.is_valid
import LeanZKCircuit.Command.Air.structure_definition
import LeanZKCircuit.Command.Air.valid_circuit
import LeanZKCircuit.Command.Air.Lemmas.base_member_projection
import LeanZKCircuit.Command.Air.Lemmas.subcircuit_isValid
import LeanZKCircuit.Command.util

open Lean Parser

def define_air
  (circuit_definition: CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  define_raw_air_structure circuit_definition log
  create_raw_circuit_instance circuit_definition log
  assign_raw_circuit_columns circuit_definition log
  define_circuit_isValid circuit_definition log
  create_subcircuit_isValid_of_isValid_lemmas circuit_definition log
  define_valid_circuit_abbrev circuit_definition log
  create_valid_circuit_base_projections circuit_definition log
  create_valid_circuit_custom_member_projections circuit_definition log
  create_valid_circuit_instance circuit_definition log
  create_all_valid_base_member_projection_lemmas circuit_definition log
  prove_valid_circuit_column_assignments circuit_definition log
  pure ()

elab "#define_air" defn: circuit_definition : command => do
  let parsed_defn: CircuitDefinition := ←parse_circuit_definition defn
  define_air parsed_defn

elab "#define_air?" defn: circuit_definition : command => do
  let parsed_defn: CircuitDefinition := ←parse_circuit_definition (circuit_definition := defn) (log := true)
  define_air parsed_defn (log := true)


-- #define_air? "TestSubAirType" using "openvm_encapsulation" where
--   Column["test_subcolumn"]

-- #define_air? "TestCircuit" using "openvm_encapsulation" where
--   Column["test_column"]
--   SubAir["test_subair" : "TestSubAirType" width := 3]
