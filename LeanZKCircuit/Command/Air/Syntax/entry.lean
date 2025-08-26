import Mathlib

open Lean

syntax air_entry :=
  ("Column[" str "]") <|>
  ("MainSubAir[" str ":" str "width" ":=" num "]") <|>
  ("PreprocessedSubAir[" str ":" str "width" ":=" num "]")

syntax subair_entry :=
  ("Column[" str "]") <|>
  ("SubAir[" str ":" str "width" ":=" num "]")

inductive AirEntry
  | column (name: String)
  | main_subair (name: String) (typeName: String) (width: ℕ)
  | preprocessed_subair (name: String) (typeName: String) (width: ℕ)

inductive SubAirEntry
  | column (name: String)
  | subair (name: String) (typeName: String) (width: ℕ)

def AirEntry.name (entry: AirEntry) : String := match entry with
  | column name => name
  | main_subair name _ _ => name
  | preprocessed_subair name _ _ => name

def SubAirEntry.name (entry: SubAirEntry) : String := match entry with
  | column name => name
  | subair name _ _ => name

instance : ToMessageData AirEntry where
  toMessageData := λ entry => match entry with
    | .column name => s!"Column[{name}]"
    | .main_subair name typeName width => s!"Main SubAir[{name} : {typeName} width := {width}]"
    | .preprocessed_subair name typeName width => s!"Preprocessed SubAir[{name} : {typeName} width := {width}]"

instance : ToMessageData SubAirEntry where
  toMessageData := λ entry => match entry with
    | .column name => s!"Column[{name}]"
    | .subair name typeName width => s!"SubAir[{name} : {typeName} width := {width}]"

/--
Parsing entries is troublesome because lean will easily match either category even when they do not match fully,
so here we do the transformation once and map to a properly tagged inductive

REVIEW: A single match?
-/
def parse_air_entry (entry: TSyntax `air_entry) (log : Bool := false) : Elab.Command.CommandElabM AirEntry := do
  let entry := match entry with
    | `(air_entry| MainSubAir[$name:str : $typeName:str width := $w:num]) =>
      pure (AirEntry.main_subair name.getString typeName.getString w.getNat)
    | _ => match entry with
      | `(air_entry| PreprocessedSubAir[$name:str : $typeName:str width := $w:num]) =>
        pure (AirEntry.preprocessed_subair name.getString typeName.getString w.getNat)
      | _ => match entry with
        | `(air_entry| Column[$name]) =>
          pure (AirEntry.column name.getString)
        | _ => throwError "failed to parse air entry"

  if log then
    logInfo m!"{←entry}"

  entry

def parse_subair_entry (entry: TSyntax `subair_entry) (log : Bool := false) : Elab.Command.CommandElabM SubAirEntry := do
  let entry := match entry with
    | `(subair_entry| SubAir[$name:str : $typeName:str width := $w:num]) =>
      pure (SubAirEntry.subair name.getString typeName.getString w.getNat)
      | _ => match entry with
        | `(subair_entry| Column[$name]) =>
          pure (SubAirEntry.column name.getString)
        | _ => throwError "failed to parse subair entry"

  if log then
    logInfo m!"{←entry}"

  entry
