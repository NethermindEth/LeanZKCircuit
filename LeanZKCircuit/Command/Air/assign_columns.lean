import LeanZKCircuit.Command.Air.Syntax.air_definition
import LeanZKCircuit.Command.util

open Lean

-- produces a list of corresponding AIR columns and subAIR columns
def calculate_air_column_assignments
  (defn: AirDefinition)
: List (String × String) :=
  (defn.entries.foldl (λ (acc: ℕ × List (String × String)) (x: AirEntry) =>
    let offset := acc.1
    let assignments := acc.2
    match x with
      | .column name => (offset + 1, assignments.concat (
        s!"main (id := 0) (column := {offset})",
        name
      ))
      | .main_subair name _ width => (
          offset + width,
          assignments.append (
            (List.range width
              ).map λ index => (
                s!"main (id := 0) (column := {offset + index})",
                s!"{name}.columns (column := {index})"
              )
          )
        )
      | .preprocessed_subair name _ width => (
          offset + width,
          assignments.append (
            (List.range width
              ).map λ index => (
                s!"preprocessed (column := {offset + index})",
                s!"{name}.columns (column := {index})"
              )
          )
        )
  ) (0, [])).2

def calculate_subair_column_assignments
  (defn: SubAirDefinition)
: List (String × String) :=
  (defn.entries.foldl (λ (acc: ℕ × List (String × String)) (x: SubAirEntry) =>
    let offset := acc.1
    let assignments := acc.2
    match x with
      | .column name => (offset + 1, assignments.concat (
          s!"columns (column := {offset})",
          name
        ))
      | .subair name _ width => (
          offset + width,
          assignments.append (
            (List.range width
              ).map λ index => (
                s!"columns (column := {offset + index})",
                s!"{name}.columns (column := {index})"
              )
          )
        )
  ) (0, [])).2

def define_column_assignment
  (circuit: String) (simp_attribute: String) (type_params: String) (col: String) (member: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"def {circuit}.col_{col} {"{"}{type_params}{"}"}\n" ++
    s!"  (c: {circuit} {type_params}) (row: ℕ) (rotation: ℕ)\n" ++
    s!": Prop :=\n" ++
    s!"  c.{col} (row := row) (rotation := rotation) =\n" ++
    s!"  c.{member} (row := row) (rotation := rotation)"
  runAsCommand command log

def assign_raw_air_columns
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let column_assignments := calculate_air_column_assignments defn
  if log then logInfo m!"Calculated air column assignments:\n{column_assignments}"

  discard (column_assignments.mapM (λ assignment =>
    let col := assignment.1
    let member := assignment.2
    define_column_assignment s!"Raw_{defn.name}" defn.simp_attribute "F ExtF" col member log
  ))

def assign_raw_subair_columns
  (defn: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let column_assignments := calculate_subair_column_assignments defn
  if log then logInfo m!"Calculated subair column assignments:\n{column_assignments}"

  discard (column_assignments.mapM (λ assignment =>
    let col := assignment.1
    let member := assignment.2
    define_column_assignment s!"Raw_{defn.name}" defn.simp_attribute "F" col member log
  ))
