import LeanZKCircuit.Command.Air.Syntax.air_definition
import LeanZKCircuit.Command.util

open Lean Parser


def create_circuit_instance
  (name: String) (log: Bool := false)
: Elab.Command.CommandElabM Unit := do
  let instance_string : String :=
    s!"instance {"{"}F ExtF{"}"} [Field F] [Field ExtF] : Circuit F ExtF {name} where\n" ++
    s!"  buses := {name}.buses\n" ++
    s!"  challenge := {name}.challenge\n" ++
    s!"  exposed := {name}.exposed\n" ++
    s!"  main := {name}.main\n" ++
    s!"  permutation := {name}.permutation\n" ++
    s!"  preprocessed := {name}.preprocessed\n" ++
    s!"  public_values := {name}.public_values\n" ++
    s!"  last_row := {name}.last_row"

  runAsCommand instance_string log

def create_raw_circuit_instance
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit :=
  create_circuit_instance s!"Raw_{defn.name}" log

def create_valid_circuit_instance
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit :=
  create_circuit_instance s!"Valid_{defn.name}" log
