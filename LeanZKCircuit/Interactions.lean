import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.EuclideanDomain.Field

namespace Interaction

  variable [Field F]

  @[grind]
  def balances [Field F] (i1 i2 : F × List F) : Prop :=
    i1.1 + i2.1 = 0 ∧ i1.2 = i2.2

  lemma balances_comm {i1 i2 : F × List F } :
    balances i1 i2 ↔ balances i2 i1
  := by grind

end Interaction

namespace InteractionList

  variable [BEq (List F)] [Field F]

  def get_multiplicity (list : List (F × List F)) (data : List F) : F :=
    ((list.filter (λ x => x.2 == data)).map Prod.fst).sum

  lemma get_multiplicity_append (l₁ l₂ : List (F × List F)) (data : List F) :
    get_multiplicity (l₁ ++ l₂) data = get_multiplicity l₁ data + get_multiplicity l₂ data
  := by
    unfold get_multiplicity
    simp

  lemma get_multiplicity_empty (data : List F) :
    get_multiplicity [] data = 0
  := by
    unfold get_multiplicity
    simp

  def balanced_by (l₁ l₂ : List (F × List F)) : Prop :=
    ∀ data : List F,
      get_multiplicity l₁ data +
      get_multiplicity l₂ data =
      0

  def is_balanced (list : List (F × List F)) : Prop :=
    ∀ data : List F, get_multiplicity list data = 0

  lemma append_is_balanced_of_balanced_by (l₁ l₂: List (F × List F)) (h : balanced_by l₁ l₂) :
    is_balanced (l₁ ++ l₂)
  := by
    unfold balanced_by at h
    unfold is_balanced
    intro data
    rewrite [get_multiplicity_append]
    specialize h data
    exact h

  lemma get_multiplicity_of_is_balanced (list : List (F × List F)) (data : List F) (h : is_balanced list) :
    get_multiplicity list data = 0
  := by
    unfold is_balanced at h
    exact h data

  lemma is_balanced_of_balanced_by_empty (list : List (F × List F)) (h : balanced_by list []) :
    is_balanced list
  := by
    unfold balanced_by at h
    unfold is_balanced
    intro data
    specialize h data
    rewrite [get_multiplicity_empty] at h
    simp_all

  lemma is_balanced_comm (l₁ l₂ : List (F × List F)) (h : balanced_by l₁ l₂) :
    balanced_by l₂ l₁
  := by
    unfold balanced_by at h ⊢
    intro data
    specialize h data
    grind

  lemma is_balanced_of_append_is_balanced (l₁ l₂ : List (F × List F))
    (h_l₂ : is_balanced l₂)
    (h_append : is_balanced (l₁ ++ l₂))
  :
    is_balanced l₁
  := by
    unfold is_balanced at h_l₂ h_append ⊢
    intro data
    specialize h_l₂ data
    specialize h_append data
    rewrite [get_multiplicity_append] at h_append
    simp_all

  lemma append_is_balanced_of_is_balanced (l₁ l₂ : List (F × List F))
    (h1 : is_balanced l₁)
    (h2 : is_balanced l₂)
  :
    is_balanced (l₁ ++ l₂)
  := by
    apply append_is_balanced_of_balanced_by
    unfold balanced_by
    intro data
    unfold is_balanced at h1 h2
    specialize h1 data
    specialize h2 data
    grind

  lemma is_balanced_trans (bus₁ bus₂ spec₁ spec₂ : List (F × List F))
    (h_bus₁ : balanced_by bus₁ spec₁)
    (h_bus₂ : balanced_by bus₂ spec₂)
    (h_spec : balanced_by spec₁ spec₂)
  :
    balanced_by bus₁ bus₂
  := by
    apply append_is_balanced_of_balanced_by at h_bus₁
    apply append_is_balanced_of_balanced_by at h_bus₂
    apply append_is_balanced_of_balanced_by at h_spec
    have := append_is_balanced_of_is_balanced _ _ h_bus₁ h_bus₂
    unfold is_balanced at this
    simp [get_multiplicity_append] at this
    unfold balanced_by
    intro data
    specialize this data
    unfold is_balanced at h_spec
    specialize h_spec data
    rewrite [get_multiplicity_append] at h_spec
    rewrite [←add_assoc, add_comm (get_multiplicity bus₂ _), ←add_assoc] at this
    grind

  def balanced_by_ordered [Field F] (l₁ l₂ : List (F × List F)) : Prop :=
    match l₁, l₂ with
      | [], [] => true
      | _ :: _, [] => false
      | [], _ :: _ => false
      | a :: as, b :: bs =>
        Interaction.balances a b ∧ balanced_by_ordered as bs

  omit [BEq (List F)] in
  lemma balanced_by_ordered_head_multiplicity
    {a b : (F × List F)}
    (h : balanced_by_ordered (a :: as) (b :: bs))
  : a.1 + b.1 = 0 := by
    unfold balanced_by_ordered at h
    grind

  omit [BEq (List F)] in
  lemma balanced_by_ordered_head_data
    {a b : (F × List F)}
    (h : balanced_by_ordered (a :: as) (b :: bs))
  : a.2 = b.2 := by
    unfold balanced_by_ordered at h
    grind

  omit [BEq (List F)] in
  lemma balanced_by_ordered_tail
    {a b : (F × List F)}
    (h : balanced_by_ordered (a :: as) (b :: bs))
  : balanced_by_ordered as bs := by
    unfold balanced_by_ordered at h
    grind

end InteractionList
