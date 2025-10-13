import Lean
import Qq
import Mathlib.Tactic

namespace LeanZKCircuit

set_option hygiene false in
open Lean Elab Tactic Qq in
protected partial def vectorEq : TacticM Unit := withMainContext do
  let target : Q(Prop) ← (←getMainGoal).getType
  match target with
  | ~q(_ = Vector.toArray $vQ) =>
    let ⟨.succ _, ~q(Vector _ (OfNat.ofNat $lenQ)), .fvar eQ⟩ ← inferTypeQ vQ
      | throwError "Expected `_ = v.toArray`."
    let e := mkIdent (←eQ.getUserName)
    let len := Syntax.mkNatLit lenQ.natLit!
    evalTactic <| ←`(tactic|(
      rcases $e:ident with ⟨⟨e⟩, he⟩
      simp only [Vector.getElem_mk, List.getElem_toArray, Array.mk.injEq]
      iterate $len
        (rcases e with _ | ⟨_, e⟩ <;>
          [
            simp only [
              List.size_toArray, List.length_cons, List.length_nil,
              Nat.zero_add, Nat.reduceEqDiff
            ] at he;
            skip
          ])
      simp only [
        List.size_toArray, List.length_cons, Nat.reduceEqDiff, List.length_eq_zero_iff
      ] at he
      subst he
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    ))
  | ~q(Vector.toArray $vQ = $rhsQ) => liftMetaTactic' MVarId.applySymm; LeanZKCircuit.vectorEq
  | _ => throwError ""

/--
`vector_eq` proves targets of shape `vec.toArray = #[vec[0], ..., [vec[vec.length - 1]]]`.
-/
scoped elab "vector_eq" : tactic => LeanZKCircuit.vectorEq

end LeanZKCircuit
