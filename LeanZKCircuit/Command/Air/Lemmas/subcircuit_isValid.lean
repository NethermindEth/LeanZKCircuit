import LeanZKCircuit.Command.Air.Syntax.air_definition
import LeanZKCircuit.Command.util

open Lean

def create_subcircuit_isValid_of_isValid_lemma
  (circuit: String) (simp_attribute: String) (type_params: String) (proof : String) (member: String) (idx: ℕ) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let proof := s!"{proof}.1{transformIndex idx}"
  let command :=
    s!"@[{simp_attribute}]\n" ++
    s!"lemma Raw_{circuit}.subcircuit_{member}_isValid_of_isValid {"{"}{type_params}{"}"}\n" ++
    s!"  (c: Raw_{circuit} {type_params}) (h: c.isValid) :\n" ++
    s!"c.{member}.isValid := by\n" ++
    s!"  exact {proof}"

  runAsCommand command log

def create_air_subair_isValid_of_isValid_lemmas
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  discard ((defn.entries.filterMap (λ entry =>
    match entry with
      | .column _ => .none
      | .main_subair name _ _ => .some name
      | .preprocessed_subair name _ _ => .some name
  )).mapIdxM (
    λ idx name =>
      create_subcircuit_isValid_of_isValid_lemma
        defn.name
        defn.simp_attribute
        "F ExtF"
        "h.2"
        name
        idx
        log
  ))

def create_subair_subair_isValid_of_isValid_lemmas
  (defn: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  discard ((defn.entries.filterMap (λ entry =>
    match entry with
      | .column _ => .none
      | .subair name _ _ => .some name
  )).mapIdxM (
    λ idx name =>
      create_subcircuit_isValid_of_isValid_lemma
        defn.name
        defn.simp_attribute
        "F"
        "h"
        name
        idx
        log
  ))
