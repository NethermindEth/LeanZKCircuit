import LeanZKCircuit.Command.Air.Syntax.entry

open Lean

syntax circuit_definition := str "using" str "where" entry*

structure CircuitDefinition where
  name: String
  simp_attribute: String
  entries: Array Entry

instance : ToMessageData CircuitDefinition where
  toMessageData := λ defn =>
    m!"CircuitDefintion(name: {defn.name} simp_attribute: {defn.simp_attribute} entries: {defn.entries})"

def parse_circuit_definition (circuit_definition: TSyntax `circuit_definition) (log : Bool := false) : Elab.Command.CommandElabM CircuitDefinition := do
  let res := match circuit_definition with
    | `(circuit_definition| $name: str using $simp_attribute: str where $entries: entry*) => do
      let entries := ←entries.mapM parse_entry
      pure (
        CircuitDefinition.mk
          name.getString
          simp_attribute.getString
          entries
      )
    | _ => throwError "Failed to parse circuit definition"
  if log then
    logInfo m!"{←res}"
  else
    pure ()

  res
