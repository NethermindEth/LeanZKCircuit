import Mathlib

structure Circuit (F: Type) [Field F] (ExtF: Type) [Field ExtF] where -- should these be parameters or members?
  buses: (index: ℕ) -> List (F × List F)
  challenge: (index: ℕ) -> ExtF
  exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
  main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
  preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  public_values: (index: ℕ) -> F
  last_row: ℕ

def Circuit.isFirstRow [Field F] [Field ExtF] (_c: Circuit F ExtF) (row: ℕ): F :=
  if row = 0 then 1 else 0
def Circuit.isLastRow [Field F] [Field ExtF] (c: Circuit F ExtF) (row: ℕ): F :=
  if row = c.last_row then 1 else 0
def Circuit.isTransitionRow [Field F] [Field ExtF] (c: Circuit F ExtF) (row: ℕ): F :=
  if row = c.last_row then 0 else 1

register_simp_attr openvm_encapsulation

#min_imports
