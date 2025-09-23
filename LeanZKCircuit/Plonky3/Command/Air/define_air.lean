import LeanZKCircuit.Plonky3.Command.Air.Lemmas.base_member_projection
import LeanZKCircuit.Plonky3.Command.Air.Lemmas.subcircuit_isValid
import LeanZKCircuit.Plonky3.Command.Air.instance_creation
import LeanZKCircuit.Plonky3.Command.Air.is_valid
import LeanZKCircuit.Plonky3.Command.Air.structure_definition
import LeanZKCircuit.Plonky3.Command.Air.valid_circuit

import LeanZKCircuit.Plonky3.Circuit

open Lean Parser

namespace Plonky3
def check_air_member_names
  (defn: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  if log then logInfo m!"Checking member names do not clash with Circuit members"

  if defn.entries.any (λ x => x.name == "bus") then
    throwError "Bus cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "challenge") then
    throwError "challenge cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "main") then
    throwError "main cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "permutation") then
    throwError "permutation cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "preprocessed") then
    throwError "preprocessed cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "public_values") then
    throwError "public_values cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "last_row") then
    throwError "last_row cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isFirstRow") then
    throwError "isFirstRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isLastRow") then
    throwError "isLastRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isTransitionRow") then
    throwError "isTransitionRow cannot be used as a member name"

def check_subair_member_names
  (defn: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  if log then logInfo m!"Checking member names do not clash with Circuit members"

  if defn.entries.any (λ x => x.name == "bus") then
    throwError "bus cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "challenge") then
    throwError "challenge cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "main") then
    throwError "main cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "permutation") then
    throwError "permutation cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "preprocessed") then
    throwError "preprocessed cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "public_values") then
    throwError "public_values cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "last_row") then
    throwError "last_row cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isFirstRow") then
    throwError "isFirstRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isLastRow") then
    throwError "isLastRow cannot be used as a member name"
  else if defn.entries.any (λ x => x.name == "isTransitionRow") then
    throwError "isTransitionRow cannot be used as a member name"

def define_air
  (air_definition: AirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  check_air_member_names air_definition log
  define_raw_air_structure air_definition log
  create_raw_circuit_instance air_definition log
  assign_raw_air_columns air_definition log
  define_air_isValid air_definition log
  create_air_subair_isValid_of_isValid_lemmas air_definition log
  define_air_valid_circuit_abbrev air_definition log
  create_air_valid_circuit_base_projections air_definition log
  create_air_valid_circuit_custom_member_projections air_definition log
  create_valid_circuit_instance air_definition log
  create_all_air_valid_base_member_projection_lemmas air_definition log
  prove_valid_air_column_assignments air_definition log
  pure ()

def define_subair
  (subair_definition: SubAirDefinition) (log : Bool := false)
: Elab.Command.CommandElabM Unit := do
  check_subair_member_names subair_definition
  define_raw_subair_structure subair_definition log
  assign_raw_subair_columns subair_definition log
  define_subair_isValid subair_definition log
  create_subair_subair_isValid_of_isValid_lemmas subair_definition log
  define_subair_valid_circuit_abbrev subair_definition log
  create_subair_valid_circuit_base_projections subair_definition log
  create_subair_valid_circuit_custom_member_projections subair_definition log
  prove_valid_subair_column_assignments subair_definition log
  pure ()

elab "#define_air" defn: air_definition : command => do
  let parsed_defn: AirDefinition := ←parse_air_definition defn
  define_air parsed_defn

elab "#define_air?" defn: air_definition : command => do
  logInfo m!"Defining Plonky3 air"
  let parsed_defn: AirDefinition := ←parse_air_definition (air_definition := defn) (log := true)
  define_air parsed_defn (log := true)

elab "#define_subair" defn: subair_definition : command => do
  let parsed_defn: SubAirDefinition := ←parse_subair_definition defn
  define_subair parsed_defn

elab "#define_subair?" defn: subair_definition : command => do
  let parsed_defn: SubAirDefinition := ←parse_subair_definition (subair_definition := defn) (log := true)
  define_subair parsed_defn (log := true)


#define_subair? "TestSubAirType" using "plonky3_encapsulation" where
  Column["test_subcolumn"]

#define_air? "TestCircuit" using "plonky3_encapsulation" where
  Column["test_column"]
  MainSubAir["test_subair" : "TestSubAirType" width := 3]
  PreprocessedSubAir["p_subair" : "TestSubAirType" width := 3]



structure Raw_TestCircuit (F: Type) (ExtF : Type) where
  bus : List (F × List F)
  challenge (index: ℕ) : ExtF
  main (column: ℕ) (row: ℕ) (rotation: ℕ) : F
  permutation (column: ℕ) (row: ℕ) (rotation: ℕ) : ExtF
  preprocessed (column: ℕ) (row: ℕ) (rotation: ℕ) : F
  public_values (index: ℕ) : F
  last_row: ℕ
  test_column (row : ℕ) (rotation : ℕ) : F
  test_subair : Raw_TestSubAirType F
  p_subair : Raw_TestSubAirType F

instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Raw_TestCircuit where
  bus := Raw_TestCircuit.bus
  challenge := Raw_TestCircuit.challenge
  main := Raw_TestCircuit.main
  permutation := Raw_TestCircuit.permutation
  preprocessed := Raw_TestCircuit.preprocessed
  public_values := Raw_TestCircuit.public_values
  last_row := Raw_TestCircuit.last_row

@[plonky3_encapsulation]
def Raw_TestCircuit.col_0 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.main (column := 0) (row := row) (rotation := rotation) =
  c.test_column (row := row) (rotation := rotation)

@[plonky3_encapsulation]
def Raw_TestCircuit.col_1 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.main (column := 1) (row := row) (rotation := rotation) =
  c.test_subair.columns (column := 0) (row := row) (rotation := rotation)

@[plonky3_encapsulation]
def Raw_TestCircuit.col_2 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.main (column := 2) (row := row) (rotation := rotation) =
  c.test_subair.columns (column := 1) (row := row) (rotation := rotation)

@[plonky3_encapsulation]
def Raw_TestCircuit.col_3 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.main (column := 3) (row := row) (rotation := rotation) =
  c.test_subair.columns (column := 2) (row := row) (rotation := rotation)

@[plonky3_encapsulation]
def Raw_TestCircuit.col_4 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.preprocessed (column := 0) (row := row) (rotation := rotation) =
  c.p_subair.columns (column := 0) (row := row) (rotation := rotation)

@[plonky3_encapsulation]
def Raw_TestCircuit.col_5 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.preprocessed (column := 1) (row := row) (rotation := rotation) =
  c.p_subair.columns (column := 1) (row := row) (rotation := rotation)

@[plonky3_encapsulation]
def Raw_TestCircuit.col_6 {F ExtF}
  (c: Raw_TestCircuit F ExtF) (row: ℕ) (rotation: ℕ)
: Prop :=
  c.preprocessed (column := 2) (row := row) (rotation := rotation) =
  c.p_subair.columns (column := 2) (row := row) (rotation := rotation)

def Raw_TestCircuit.isValid {F ExtF}
  (c: Raw_TestCircuit F ExtF)
: Prop :=
  (∀ column row rotation,
    c.main column row rotation = c.main column ((row + rotation) % (c.last_row + 1)) 0 ∧
    c.permutation column row rotation = c.permutation column ((row + rotation) % (c.last_row + 1)) 0 ∧
    c.preprocessed column row rotation = c.preprocessed column ((row + rotation) % (c.last_row + 1)) 0
  ) ∧
  (c.test_subair.isValid ∧ c.p_subair.isValid ∧ true) ∧
  (∀ row rotation, c.col_0 row rotation ∧ c.col_1 row rotation ∧ c.col_2 row rotation ∧ c.col_3 row rotation ∧ c.col_4 row rotation ∧ c.col_5 row rotation ∧ c.col_6 row rotation ∧ true)

@[plonky3_encapsulation]
lemma Raw_TestCircuit.subcircuit_test_subair_isValid_of_isValid {F ExtF}
  (c: Raw_TestCircuit F ExtF) (h: c.isValid) :
c.test_subair.isValid := by
  exact h.2.1.1

@[plonky3_encapsulation]
lemma Raw_TestCircuit.subcircuit_p_subair_isValid_of_isValid {F ExtF}
  (c: Raw_TestCircuit F ExtF) (h: c.isValid) :
c.p_subair.isValid := by
  exact h.2.1.2.1

abbrev Valid_TestCircuit
  (F: Type) (ExtF: Type)
:=
  { c : Raw_TestCircuit F ExtF // c.isValid }

abbrev Valid_TestCircuit.bus {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.bus

abbrev Valid_TestCircuit.challenge {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.challenge

abbrev Valid_TestCircuit.main {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.main

abbrev Valid_TestCircuit.permutation {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.permutation

abbrev Valid_TestCircuit.preprocessed {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.preprocessed

abbrev Valid_TestCircuit.public_values {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.public_values

abbrev Valid_TestCircuit.last_row {F ExtF}
  (c : Valid_TestCircuit F ExtF)
:=
  c.1.last_row

def Valid_TestCircuit.test_column {F ExtF}
  (c : Valid_TestCircuit F ExtF) (row rotation : ℕ)
: F :=
  c.1.test_column row rotation

def Valid_TestCircuit.test_subair {F ExtF}
  (c : Valid_TestCircuit F ExtF)
: Valid_TestSubAirType F := ⟨
  c.1.test_subair,
  c.1.subcircuit_test_subair_isValid_of_isValid c.2
⟩

def Valid_TestCircuit.p_subair {F ExtF}
  (c : Valid_TestCircuit F ExtF)
: Valid_TestSubAirType F := ⟨
  c.1.p_subair,
  c.1.subcircuit_p_subair_isValid_of_isValid c.2
⟩

instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Valid_TestCircuit where
  bus := Valid_TestCircuit.bus
  challenge := Valid_TestCircuit.challenge
  main := Valid_TestCircuit.main
  permutation := Valid_TestCircuit.permutation
  preprocessed := Valid_TestCircuit.preprocessed
  public_values := Valid_TestCircuit.public_values
  last_row := Valid_TestCircuit.last_row

@[plonky3_encapsulation]
lemma Valid_TestCircuit_bus_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.bus F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.bus :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit_challenge_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.challenge F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.challenge :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit_main_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.main F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.main :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit_permutation_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.permutation F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.permutation :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit_preprocessed_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.preprocessed F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.preprocessed :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit_public_values_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.public_values F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.public_values :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit_last_row_project {F ExtF}
  (c: Valid_TestCircuit F ExtF) [Field F] [Field ExtF] :
@Circuit.last_row F (by assumption) ExtF (by assumption) Valid_TestCircuit _ c = c.last_row :=
  rfl

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_0 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.main (column := 0) row rotation = c.test_column row rotation :=
  (c.2.2.2 row rotation).1

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_1 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.main (column := 1) row rotation = c.test_subair.columns (column := 0) row rotation :=
  (c.2.2.2 row rotation).2.1

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_2 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.main (column := 2) row rotation = c.test_subair.columns (column := 1) row rotation :=
  (c.2.2.2 row rotation).2.2.1

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_3 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.main (column := 3) row rotation = c.test_subair.columns (column := 2) row rotation :=
  (c.2.2.2 row rotation).2.2.2.1

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_4 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.preprocessed (column := 0) row rotation = c.p_subair.columns (column := 0) row rotation :=
  (c.2.2.2 row rotation).2.2.2.2.1

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_5 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.preprocessed (column := 1) row rotation = c.p_subair.columns (column := 1) row rotation :=
  (c.2.2.2 row rotation).2.2.2.2.2.1

@[plonky3_encapsulation]
lemma Valid_TestCircuit.col_6 {F ExtF} [Field F] [Field ExtF]
  (c : Valid_TestCircuit F ExtF) (row rotation: ℕ) :
c.preprocessed (column := 2) row rotation = c.p_subair.columns (column := 2) row rotation :=
  (c.2.2.2 row rotation).2.2.2.2.2.2.1

end Plonky3
