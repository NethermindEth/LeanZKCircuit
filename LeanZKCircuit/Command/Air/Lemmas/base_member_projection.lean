import LeanZKCircuit.Command.Air.Syntax.circuit_definition
import LeanZKCircuit.Command.util

open Lean

def create_base_member_projection_lemma
  (circuit: String) (simp_attribute: String) (member: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  let lemma_string :=
    s!"@[{simp_attribute}]\n" ++
    s!"lemma {circuit}_{member}_project {"{"}F ExtF{"}"}\n" ++
    s!"  (c: {circuit} F ExtF) [Field F] [Field ExtF] :\n" ++
    s!"@Circuit.{member} F (by assumption) ExtF (by assumption) {circuit} _ c = c.{member} :=\n" ++
    s!"  rfl"
  runAsCommand lemma_string log

def create_all_base_member_projection_lemmas
  (circuit: String) (simp_attribute: String) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  create_base_member_projection_lemma circuit simp_attribute "buses" log
  create_base_member_projection_lemma circuit simp_attribute "challenge" log
  create_base_member_projection_lemma circuit simp_attribute "exposed" log
  create_base_member_projection_lemma circuit simp_attribute "main" log
  create_base_member_projection_lemma circuit simp_attribute "permutation" log
  create_base_member_projection_lemma circuit simp_attribute "preprocessed" log
  create_base_member_projection_lemma circuit simp_attribute "public_values" log
  create_base_member_projection_lemma circuit simp_attribute "last_row" log

def create_all_valid_base_member_projection_lemmas
  (defn: CircuitDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  create_all_base_member_projection_lemmas s!"Valid_{defn.name}" defn.simp_attribute log
