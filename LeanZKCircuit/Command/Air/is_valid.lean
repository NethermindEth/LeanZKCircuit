import LeanZKCircuit.Command.Air.assign_columns
import LeanZKCircuit.Command.util

open Lean

def isValid_air_recursion_term
  (defn: AirDefinition)
: String :=
  defn.entries.foldr (λ entry acc =>
    match entry with
      | .column _ => acc
      | .main_subair name _ _ => s!"c.{name}.isValid ∧ {acc}"
      | .preprocessed_subair name _ _ => s!"c.{name}.isValid ∧ {acc}"
  ) "true"

def isValid_subair_recursion_term
  (defn: SubAirDefinition)
: String :=
  defn.entries.foldr (λ entry acc =>
    match entry with
      | .column _ => acc
      | .subair name _ _ => s!"c.{name}.isValid ∧ {acc}"
  ) "true"

def isValid_column_assignments_term
  (num_columns: ℕ)
: String :=
  (List.range num_columns).foldr (λ n acc => s!"c.col_{n} row rotation ∧ {acc}") "true"

def define_air_isValid
  (defn : AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let subair_term := isValid_air_recursion_term defn
  let num_columns := (calculate_air_column_assignments defn).length
  let columns_term := isValid_column_assignments_term num_columns
  let command :=
    s!"def Raw_{defn.name}.isValid {"{"}F ExtF{"}"}\n" ++
    s!"  (c: Raw_{defn.name} F ExtF)\n" ++
    s!": Prop :=\n" ++
    s!"  (∀ id column row rotation,\n" ++
    s!"    c.main id column row rotation = c.main id column ((row + rotation) % (c.last_row + 1)) 0 ∧\n" ++
    s!"    c.permutation column row rotation = c.permutation column ((row + rotation) % (c.last_row + 1)) 0 ∧\n" ++
    s!"    c.preprocessed column row rotation = c.preprocessed column ((row + rotation) % (c.last_row + 1)) 0\n" ++
    s!"  ) ∧\n" ++
    s!"  ({subair_term}) ∧\n" ++
    s!"  (∀ row rotation, {columns_term})"
  runAsCommand command log

def define_subair_isValid
  (defn : SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let subair_term := isValid_subair_recursion_term defn
  let num_columns := (calculate_subair_column_assignments defn).length
  let columns_term := isValid_column_assignments_term num_columns
  let command :=
    s!"def Raw_{defn.name}.isValid {"{"}F{"}"}\n" ++
    s!"  (c: Raw_{defn.name} F)\n" ++
    s!": Prop :=\n" ++
    s!"  ({subair_term}) ∧\n" ++
    s!"  (∀ row rotation, {columns_term})"
  runAsCommand command log
