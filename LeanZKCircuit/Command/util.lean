import Mathlib

open Lean Parser

def runAsCommand (command_string: String) (log: Bool := false): Elab.Command.CommandElabM Unit := do
  if log then
    logInfo m!"Running command:\n{command_string}"
  else
    pure ()

  let .ok command_string_stx := runParserCategory (← getEnv) `command command_string
    | throwError s!"Failed to parse command {command_string}"
  let command_string_tstx : TSyntax `command := ⟨command_string_stx⟩
  Lean.Elab.Command.elabCommand command_string_tstx

-- Converts a numeric index into an accessor in a nested structure
-- Note that the structure must have a placeholder final member for this to work
-- e.g. this will work to get the third element from a ∧ b ∧ c ∧ d ∧ true,
-- but not to get the third element from a ∧ b ∧ c
def transformIndex (n: ℕ): String :=
      match n with
        | 0 => ".1"
        | m+1 =>
          let r := transformIndex m
          s!".2{r}"
