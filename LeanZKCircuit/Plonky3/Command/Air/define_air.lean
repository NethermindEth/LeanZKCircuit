import LeanZKCircuit.Plonky3.Command.Air.Lemmas.base_member_projection
import LeanZKCircuit.Plonky3.Command.Air.Lemmas.subcircuit_isValid
import LeanZKCircuit.Plonky3.Command.Air.instance_creation
import LeanZKCircuit.Plonky3.Command.Air.is_valid
import LeanZKCircuit.Plonky3.Command.Air.structure_definition
import LeanZKCircuit.Plonky3.Command.Air.valid_circuit

import LeanZKCircuit.Plonky3.Circuit

open Lean Parser

namespace Plonky3
def check_air_member_names
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  if log then logInfo m!"Checking member names do not clash with Circuit members"

  if defn.entries.any (λ x => x.name == "bus") then
    throwError "Bus cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "challenge") then
    throwError "challenge cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "main") then
    throwError "main cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "permutation") then
    throwError "permutation cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "preprocessed") then
    throwError "preprocessed cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "public_values") then
    throwError "public_values cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "last_row") then
    throwError "last_row cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isFirstRow") then
    throwError "isFirstRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isLastRow") then
    throwError "isLastRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isTransitionRow") then
    throwError "isTransitionRow cannot be used as a member name"

def check_subair_member_names
  (defn: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  if log then logInfo m!"Checking member names do not clash with Circuit members"

  if defn.entries.any (λ x => x.name == "bus") then
    throwError "bus cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "challenge") then
    throwError "challenge cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "main") then
    throwError "main cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "permutation") then
    throwError "permutation cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "preprocessed") then
    throwError "preprocessed cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "public_values") then
    throwError "public_values cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "last_row") then
    throwError "last_row cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isFirstRow") then
    throwError "isFirstRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isLastRow") then
    throwError "isLastRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isTransitionRow") then
    throwError "isTransitionRow cannot be used as a member name"

def define_air
  (air_definition: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  check_air_member_names air_definition log
  define_raw_air_structure air_definition log
  create_raw_circuit_instance air_definition log
  assign_raw_air_columns air_definition log
  define_air_isValid air_definition log
  create_air_subair_isValid_of_isValid_lemmas air_definition log
  define_air_valid_circuit_abbrev air_definition log
  create_air_valid_circuit_base_projections air_definition log
  create_air_valid_circuit_custom_member_projections air_definition log
  create_valid_circuit_instance air_definition log
  create_all_air_valid_base_member_projection_lemmas air_definition log
  prove_valid_air_column_assignments air_definition log
  pure ()

def define_subair
  (subair_definition: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  check_subair_member_names subair_definition
  define_raw_subair_structure subair_definition log
  assign_raw_subair_columns subair_definition log
  define_subair_isValid subair_definition log
  create_subair_subair_isValid_of_isValid_lemmas subair_definition log
  define_subair_valid_circuit_abbrev subair_definition log
  create_subair_valid_circuit_base_projections subair_definition log
  create_subair_valid_circuit_custom_member_projections subair_definition log
  prove_valid_subair_column_assignments subair_definition log
  pure ()

elab "#define_air" defn: air_definition : command => do
  let parsed_defn: AirDefinition := ←parse_air_definition defn
  define_air parsed_defn

elab "#define_air?" defn: air_definition : command => do
  logInfo m!"Defining Plonky3 air"
  let parsed_defn: AirDefinition := ←parse_air_definition (air_definition := defn) (log := true)
  define_air parsed_defn (log := true)

elab "#define_subair" defn: subair_definition : command => do
  let parsed_defn: SubAirDefinition := ←parse_subair_definition defn
  define_subair parsed_defn

elab "#define_subair?" defn: subair_definition : command => do
  let parsed_defn: SubAirDefinition := ←parse_subair_definition (subair_definition := defn) (log := true)
  define_subair parsed_defn (log := true)


#define_subair? "TestSubAirType" using "plonky3_encapsulation" where
  Column["test_subcolumn"]

#define_air? "TestCircuit" using "plonky3_encapsulation" where
  Column["test_column"]
  MainSubAir["test_subair" : "TestSubAirType" width := 3]
  PreprocessedSubAir["p_subair" : "TestSubAirType" width := 3]


end Plonky3
