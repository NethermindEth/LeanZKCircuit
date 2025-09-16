import LeanZKCircuit.Plonky3.Command.Air.Syntax.air_definition
import LeanZKCircuit.Plonky3.Command.Air.assign_columns
import LeanZKCircuit.Plonky3.Command.util

open Lean

namespace Plonky3
def define_air_valid_circuit_abbrev
  (defn : AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"abbrev Valid_{defn.name}\n" ++
    s!"  (F: Type) (ExtF: Type)\n" ++
    s!":=\n" ++
    s!"  {"{"} c : Raw_{defn.name} F ExtF // c.isValid {"}"}"
  runAsCommand command log

def define_subair_valid_circuit_abbrev
  (defn : SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"abbrev Valid_{defn.name}\n" ++
    s!"  (F: Type)\n" ++
    s!":=\n" ++
    s!"  {"{"} c : Raw_{defn.name} F // c.isValid {"}"}"
  runAsCommand command log

def create_valid_circuit_base_projection
  (name : String) (member : String) (type_params: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"abbrev Valid_{name}.{member} {"{"}{type_params}{"}"}\n" ++
    s!"  (c : Valid_{name} {type_params})\n" ++
    s!":=\n" ++
    s!"  c.1.{member}"

  runAsCommand command log

def create_air_valid_circuit_base_projections
  (defn : AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  create_valid_circuit_base_projection defn.name "bus" "F ExtF" log
  create_valid_circuit_base_projection defn.name "challenge" "F ExtF" log
  create_valid_circuit_base_projection defn.name "main" "F ExtF" log
  create_valid_circuit_base_projection defn.name "permutation" "F ExtF" log
  create_valid_circuit_base_projection defn.name "preprocessed" "F ExtF" log
  create_valid_circuit_base_projection defn.name "public_values" "F ExtF" log
  create_valid_circuit_base_projection defn.name "last_row" "F ExtF" log

def create_subair_valid_circuit_base_projections
  (defn : SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  create_valid_circuit_base_projection defn.name "columns" "F" log

def create_valid_circuit_column_projection
  (circuit : String) (column : String) (type_params: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"def Valid_{circuit}.{column} {"{"}{type_params}{"}"}\n" ++
    s!"  (c : Valid_{circuit} {type_params}) (row rotation : ℕ)\n" ++
    s!": F :=\n" ++
    s!"  c.1.{column} row rotation"

  runAsCommand command log

def create_valid_circuit_subair_projection
  (circuit : String) (subair_name : String) (subair_type : String) (type_params: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"def Valid_{circuit}.{subair_name} {"{"}{type_params}{"}"}\n" ++
    s!"  (c : Valid_{circuit} {type_params})\n" ++
    s!": Valid_{subair_type} F := ⟨\n" ++
    s!"  c.1.{subair_name},\n" ++
    s!"  c.1.subcircuit_{subair_name}_isValid_of_isValid c.2\n" ++
    s!"⟩"

  runAsCommand command log

def create_air_valid_circuit_custom_member_projections
  (defn : AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  defn.entries.forM λ entry =>
    match entry with
      | .column name =>
        create_valid_circuit_column_projection defn.name name "F ExtF" log
      | .main_subair name typename _ =>
        create_valid_circuit_subair_projection defn.name name typename "F ExtF" log
      | .preprocessed_subair name typename _ =>
        create_valid_circuit_subair_projection defn.name name typename "F ExtF" log

def create_subair_valid_circuit_custom_member_projections
  (defn : SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  defn.entries.forM λ entry =>
    match entry with
      | .column name =>
        create_valid_circuit_column_projection defn.name name "F" log
      | .subair name typename _ =>
        create_valid_circuit_subair_projection defn.name name typename "F" log

def prove_air_valid_circuit_column_assignment
  (circuit : String) (simp_attribute: String) (pos: ℕ) (column : String) (member : String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"lemma Valid_{circuit}.col_{pos} {"{"}F ExtF{"}"} [Field F] [Field ExtF]\n" ++
    s!"  (c : Valid_{circuit} F ExtF) (row rotation: ℕ) :\n" ++
    s!"c.{column} row rotation = c.{member} row rotation :=\n" ++
    s!"  (c.2.2 row rotation){transformIndex pos}"
  runAsCommand command log

def prove_subair_valid_circuit_column_assignment
  (circuit : String) (simp_attribute: String) (pos: ℕ) (column : String) (member : String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"lemma Valid_{circuit}.col_{pos} {"{"}F{"}"} [Field F]\n" ++
    s!"  (c : Valid_{circuit} F) (row rotation: ℕ) :\n" ++
    s!"c.{column} row rotation = c.{member} row rotation :=\n" ++
    s!"  (c.2.2 row rotation){transformIndex pos}"
  runAsCommand command log

def prove_valid_air_column_assignments
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let columns := calculate_air_column_assignments defn
  discard (columns.zipIdx.mapM λ assignment =>
    let column := assignment.1.1
    let member := assignment.1.2
    let idx := assignment.2
    prove_air_valid_circuit_column_assignment
      defn.name
      defn.simp_attribute
      idx
      column
      member
      log)

def prove_valid_subair_column_assignments
  (defn: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let columns := calculate_subair_column_assignments defn
  discard (columns.zipIdx.mapM λ assignment =>
    let column := assignment.1.1
    let member := assignment.1.2
    let idx := assignment.2
    prove_subair_valid_circuit_column_assignment
      defn.name
      defn.simp_attribute
      idx
      column
      member
      log)
end Plonky3
