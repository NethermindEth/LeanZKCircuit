import LeanZKCircuit.Plonky3.Command.Air.Syntax.air_definition
import LeanZKCircuit.Plonky3.Command.util

open Lean

namespace Plonky3
-- matches the custom air members onto columns of either the main or preprocessed traces
def calculate_air_column_assignments
  (defn: AirDefinition)
: List (String × String) :=
  (defn.entries.foldl (λ (acc: (ℕ × ℕ) × List (String × String)) (x: AirEntry) =>
    let main_offset := acc.1.1
    let preprocessed_offset := acc.1.2
    let assignments := acc.2
    match x with
      | .column name => (
          (main_offset + 1, preprocessed_offset),
          assignments.concat (
            s!"main (column := {main_offset})",
            name
          )
        )
      | .main_subair name _ width => (
          (main_offset + width, preprocessed_offset),
          assignments.append (
            (List.range width
              ).map λ index => (
                s!"main (column := {main_offset + index})",
                s!"{name}.columns (column := {index})"
              )
          )
        )
      | .preprocessed_subair name _ width => (
          (main_offset, preprocessed_offset + width),
          assignments.append (
            (List.range width
              ).map λ index => (
                s!"preprocessed (column := {preprocessed_offset + index})",
                s!"{name}.columns (column := {index})"
              )
          )
        )
  ) ((0, 0), [])).2

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
  (circuit: String) (simp_attribute: String) (type_params: String) (idx: ℕ) (col: String) (member: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"def {circuit}.col_{idx} {"{"}{type_params}{"}"}\n" ++
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

  discard (column_assignments.zipIdx.mapM (λ assignment =>
    let col := assignment.1.1
    let member := assignment.1.2
    let idx := assignment.2
    define_column_assignment s!"Raw_{defn.name}" defn.simp_attribute "F ExtF" idx col member log
  ))

def assign_raw_subair_columns
  (defn: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let column_assignments := calculate_subair_column_assignments defn
  if log then logInfo m!"Calculated subair column assignments:\n{column_assignments}"

  discard (column_assignments.zipIdx.mapM (λ assignment =>
    let col := assignment.1.1
    let member := assignment.1.2
    let idx := assignment.2
    define_column_assignment s!"Raw_{defn.name}" defn.simp_attribute "F" idx col member log
  ))
end Plonky3
