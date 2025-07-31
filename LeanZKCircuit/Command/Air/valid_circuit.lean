import LeanZKCircuit.Command.Air.Syntax.circuit_definition
import LeanZKCircuit.Command.Air.assign_columns
import LeanZKCircuit.Command.util

open Lean

def define_valid_circuit_abbrev
  (defn : CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"abbrev Valid_{defn.name}\n" ++
    s!"  (F: Type) (ExtF: Type)\n" ++
    s!":=\n" ++
    s!"  {"{"} c : Raw_{defn.name} F ExtF // c.isValid {"}"}"

  runAsCommand command log

def create_valid_circuit_base_projection
  (defn : CircuitDefinition) (member : String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"abbrev Valid_{defn.name}.{member} {"{"}F ExtF{"}"}\n" ++
    s!"  (c : Valid_{defn.name} F ExtF)\n" ++
    s!":=\n" ++
    s!"  c.1.{member}"

  runAsCommand command log

def create_valid_circuit_base_projections
  (defn : CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  create_valid_circuit_base_projection defn "buses" log
  create_valid_circuit_base_projection defn "challenge" log
  create_valid_circuit_base_projection defn "exposed" log
  create_valid_circuit_base_projection defn "main" log
  create_valid_circuit_base_projection defn "permutation" log
  create_valid_circuit_base_projection defn "preprocessed" log
  create_valid_circuit_base_projection defn "public_values" log
  create_valid_circuit_base_projection defn "last_row" log

def create_valid_circuit_column_projection
  (circuit : String) (column : String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"def Valid_{circuit}.{column} {"{"}F ExtF{"}"}\n" ++
    s!"  (c : Valid_{circuit} F ExtF) (row rotation : ℕ)\n" ++
    s!": F :=\n" ++
    s!"  c.1.{column} row rotation"

  runAsCommand command log

def create_valid_circuit_subair_projection
  (circuit : String) (subair_name : String) (subair_type : String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"def Valid_{circuit}.{subair_name} {"{"}F ExtF{"}"}\n" ++
    s!"  (c : Valid_{circuit} F ExtF)\n" ++
    s!": Valid_{subair_type} F ExtF := ⟨\n" ++
    s!"  c.1.{subair_name},\n" ++
    s!"  c.1.subcircuit_{subair_name}_isValid_of_isValid c.2\n" ++
    s!"⟩"

  runAsCommand command log

def create_valid_circuit_custom_member_projections
  (defn : CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  defn.entries.forM λ entry =>
    match entry with
      | .column name =>
        create_valid_circuit_column_projection defn.name name log
      | .subair name typename _ =>
        create_valid_circuit_subair_projection defn.name name typename log

def prove_valid_circuit_column_assignment
  (circuit : String) (simp_attribute: String) (pos : ℕ) (member : String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"lemma Valid_{circuit}.col_{pos} {"{"}F ExtF{"}"} [Field F] [Field ExtF]\n" ++
    s!"  (c : Valid_{circuit} F ExtF) (row rotation: ℕ) :\n" ++
    s!"c.main 0 {pos} row rotation = c.{member} row rotation :=\n" ++
    s!"  (c.2.2 row rotation){transformIndex pos}"

  runAsCommand command log

def prove_valid_circuit_column_assignments
  (defn: CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let columns := calculate_column_assignments defn
  discard (columns.mapM λ assignment =>
    let pos := assignment.1
    let member := assignment.2
    prove_valid_circuit_column_assignment
      defn.name
      defn.simp_attribute
      pos
      member
      log)
