import Mathlib

open Lean

syntax entry := ("Column[" str "]") <|> ("SubAir[" str ":" str "width" ":=" num "]")

inductive Entry
  | column (name: String)
  | subair (name: String) (typeName: String) (width: ℕ)

instance : ToMessageData Entry where
  toMessageData := λ entry => match entry with
    | .column name => s!"Column[{name}]"
    | .subair name typeName width => s!"SubAir[{name} : {typeName} width := {width}]"

/--
Parsing entries is troublesome because lean will easily match either category even when they do not match fully,
so here we do the transformation once and map to a properly tagged inductive

REVIEW: A single match?
-/ 
def parse_entry (entry: TSyntax `entry) (log : Bool := false) : Elab.Command.CommandElabM Entry := do
  let entry := match entry with
    | `(entry| SubAir[$name:str : $typeName:str width := $w:num]) =>
      pure (Entry.subair name.getString typeName.getString w.getNat)
    | _ => match entry with
      | `(entry| Column[$name]) =>
        pure (Entry.column name.getString)
      | _ => throwError "failed to parse entry"

  if log then
    logInfo m!"{←entry}"

  entry
