import LeanZKCircuit.Command.Air.Syntax.circuit_definition
import LeanZKCircuit.Command.util

open Lean

def calculate_column_assignments
  (defn: CircuitDefinition)
: List (ℕ × String) :=
  (defn.entries.foldl (λ (acc: ℕ × List (ℕ × String)) (x: Entry) =>
    let offset := acc.1
    let assignments := acc.2
    match x with
      | .column name => (offset + 1, assignments.concat (offset, name))
      | .subair name _ width => (
          offset + width,
          assignments.append (
            (List.range width
              ).map λ index => (offset + index, s!"{name}.main (id := 0) (column := {index})")
          )
        )
  ) (0, [])).2

def define_column_assignment
  (circuit: String) (simp_attribute: String) (col: ℕ) (member: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"def {circuit}.col_{col} {"{"}F ExtF{"}"}\n" ++
    s!"  (c: {circuit} F ExtF) (row: ℕ) (rotation: ℕ)\n" ++
    s!": Prop :=\n" ++
    s!"  c.main (id := 0) (column := {col}) (row := row) (rotation := rotation) =\n" ++
    s!"  c.{member} (row := row) (rotation := rotation)"
  runAsCommand command log

def assign_raw_circuit_columns
  (defn: CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let column_assignments := calculate_column_assignments defn

  if log then
    logInfo m!"Calculated column assignments:\n{column_assignments}"
  else
    pure ()

  discard (column_assignments.mapM (λ assignment =>
    let col := assignment.1
    let member := assignment.2
    define_column_assignment s!"Raw_{defn.name}" defn.simp_attribute col member log
  ))
