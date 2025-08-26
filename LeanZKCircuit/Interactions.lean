import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.EuclideanDomain.Field

namespace Interaction

  variable [BEq (List F)] [Field F]

  def get_multiplicity (list: List (F × List F)) (data: List F) : F :=
    ((list.filter (λ x => x.2 == data)).map Prod.fst).sum

  lemma append_get_multiplicity (l₁ l₂: List (F × List F)) (data: List F):
    get_multiplicity (l₁ ++ l₂) data = get_multiplicity l₁ data + get_multiplicity l₂ data
  := by
    unfold get_multiplicity
    simp

  lemma get_multiplicity_empty (data: List F) :
    get_multiplicity [] data = 0
  := by
    unfold get_multiplicity
    simp

  def balanced_by (l₁ l₂: List (F × List F)): Prop :=
    ∀ data : List F,
      get_multiplicity l₁ data +
      get_multiplicity l₂ data =
      0

  def is_balanced (list: List (F × List F)): Prop :=
    ∀ data : List F, get_multiplicity list data = 0

  lemma append_is_balanced_of_balanced_by (l₁ l₂: List (F × List F)) (h: balanced_by l₁ l₂) :
    is_balanced (l₁ ++ l₂)
  := by
    unfold balanced_by at h
    unfold is_balanced
    intro data
    rewrite [append_get_multiplicity]
    specialize h data
    exact h

  lemma get_multiplicity_of_is_balanced (list: List (F × List F)) (data: List F) (h: is_balanced list):
    get_multiplicity list data = 0
  := by
    unfold is_balanced at h
    exact h data

  lemma is_balanced_of_balanced_by_empty (list: List (F × List F)) (h: balanced_by list []) :
    is_balanced list
  := by
    unfold balanced_by at h
    unfold is_balanced
    intro data
    specialize h data
    rewrite [get_multiplicity_empty] at h
    simp_all

end Interaction
