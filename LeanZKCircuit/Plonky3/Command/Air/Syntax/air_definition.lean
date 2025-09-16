import LeanZKCircuit.Command.Air.Syntax.entry

open Lean

namespace Plonky3
syntax air_definition := str "using" str "where" air_entry*
syntax subair_definition := str "using" str "where" subair_entry*

structure AirDefinition where
  name: String
  simp_attribute: String
  entries: Array AirEntry

structure SubAirDefinition where
  name: String
  simp_attribute: String
  entries: Array SubAirEntry

instance : ToMessageData AirDefinition where
  toMessageData := λ defn =>
    m!"AirDefintion(name: {defn.name} simp_attribute: {defn.simp_attribute} entries: {defn.entries})"

instance : ToMessageData SubAirDefinition where
  toMessageData := λ defn =>
    m!"SubAirDefintion(name: {defn.name} simp_attribute: {defn.simp_attribute} entries: {defn.entries})"

def parse_air_definition
  (air_definition: TSyntax `Plonky3.air_definition) (log : Bool := false)
: Elab.Command.CommandElabM AirDefinition := do
  let res := match air_definition with
    | `(air_definition| $name: str using $simp_attribute: str where $entries: air_entry*) => do
      let entries := ←entries.mapM parse_air_entry
      pure (
        AirDefinition.mk
          name.getString
          simp_attribute.getString
          entries
      )
    | _ => throwError "Failed to parse circuit definition"
  if log then
    logInfo m!"{←res}"

  res

def parse_subair_definition
  (subair_definition: TSyntax `Plonky3.subair_definition) (log : Bool := false)
: Elab.Command.CommandElabM SubAirDefinition := do
  let res := match subair_definition with
    | `(subair_definition| $name: str using $simp_attribute: str where $entries: subair_entry*) => do
      let entries := ←entries.mapM parse_subair_entry
      pure (
        SubAirDefinition.mk
          name.getString
          simp_attribute.getString
          entries
      )
    | _ => throwError "Failed to parse circuit definition"
  if log then
    logInfo m!"{←res}"

  res
end Plonky3
