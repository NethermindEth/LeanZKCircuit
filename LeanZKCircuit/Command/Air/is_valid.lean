import LeanZKCircuit.Command.Air.assign_columns
import LeanZKCircuit.Command.util

open Lean

def isValid_subair_term
  (defn: CircuitDefinition)
: String :=
  defn.entries.foldr (λ entry acc =>
    match entry with
      | .column _ => acc
      | .subair name _ _ => s!"c.{name}.isValid ∧ {acc}"
  ) "true"

def isValid_column_assignments_term
  (defn: CircuitDefinition)
: String :=
  let assignments := calculate_column_assignments defn
  (List.range assignments.length).foldr (λ n acc => s!"c.col_{n} row rotation ∧ {acc}") "true"

def define_circuit_isValid
  (defn : CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let subair_term := isValid_subair_term defn
  let columns_term := isValid_column_assignments_term defn
  let command :=
    s!"def Raw_{defn.name}.isValid {"{"}F ExtF{"}"}\n" ++
    s!"  (c: Raw_{defn.name} F ExtF)\n" ++
    s!": Prop :=\n" ++
    s!"  ({subair_term}) ∧\n" ++
    s!"  (∀ row rotation, {columns_term})"

  runAsCommand command log
