import Mathlib.Algebra.EuclideanDomain.Field

class Circuit (F : Type) [Field F] (ExtF : Type) [Field ExtF] (α : Type → Type → Type) where
  buses: α F ExtF → (index: ℕ) -> List (F × List F)
  challenge: α F ExtF → (index: ℕ) -> ExtF
  exposed: α F ExtF → (index: ℕ) -> ExtF
  main: α F ExtF → (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  permutation: α F ExtF → (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
  preprocessed: α F ExtF → (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  public_values: α F ExtF → (index: ℕ) -> F
  last_row: α F ExtF → ℕ

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

def Circuit.isFirstRow (_circuit : C F ExtF) (row : ℕ) : F :=
  if row = 0 then 1 else 0

def Circuit.isLastRow (circuit : C F ExtF) (row : ℕ) : F :=
  if row = Circuit.last_row circuit then 1 else 0

def Circuit.isTransitionRow (circuit : C F ExtF) (row : ℕ): F :=
  if row = Circuit.last_row circuit then 0 else 1

register_simp_attr openvm_encapsulation
