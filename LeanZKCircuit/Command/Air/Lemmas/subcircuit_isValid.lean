import LeanZKCircuit.Command.Air.Syntax.circuit_definition
import LeanZKCircuit.Command.util

open Lean

def create_subcircuit_isValid_of_isValid_lemma
  (circuit: String) (simp_attribute: String) (member: String) (idx: ℕ) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let proof := s!"h.1{transformIndex idx}"
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"lemma Raw_{circuit}.subcircuit_{member}_isValid_of_isValid {"{"}F ExtF{"}"}\n" ++
    s!"  (c: Raw_{circuit} F ExtF) (h: c.isValid) :\n" ++
    s!"c.{member}.isValid := by\n" ++
    s!"  exact {proof}"

  runAsCommand command log

def create_subcircuit_isValid_of_isValid_lemmas
  (defn: CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  discard ((defn.entries.filterMap (λ entry =>
    match entry with | .column _ => .none | .subair name _ _ => .some name
  )).mapIdxM (
    λ idx name =>
      create_subcircuit_isValid_of_isValid_lemma
        defn.name
        defn.simp_attribute
        name
        idx
        log
  ))
