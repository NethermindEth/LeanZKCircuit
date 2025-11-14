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
  | _ => throwError "Expected `vec.toArray = #[vec[0], ..., [vec[vec.length - 1]]]`"

/--
`vector_eq` proves targets of shape `vec.toArray = #[vec[0], ..., [vec[vec.length - 1]]]`.
-/
scoped elab "vector_eq" : tactic => LeanZKCircuit.vectorEq

section examples

-- set_option profiler true

-- /--
-- simp took 468ms
-- instantiate metavars took 311ms
-- elaboration took 101ms
-- -------------------------------
-- type checking took 335ms
-- -/
-- example {v : Vector ℕ 41} : v.toArray = #[
--   v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9],
--   v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18],
--   v[19], v[20], v[21], v[22], v[23], v[24], v[25], v[26], v[27],
--   v[28], v[29], v[30], v[31], v[32], v[33], v[34], v[35], v[36],
--   v[37], v[38], v[39], v[40]
-- ] := by vector_eq

-- /--
-- grind took 16.2s
-- instantiate metavars took 777ms
-- tactic execution of Lean.Parser.Tactic.grind took 321ms
-- -------------------------------------------------------
-- type checking took 3.51s
-- -/
-- example {v : Vector ℕ 41} : v.toArray = #[
--   v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9],
--   v[10], v[11], v[12], v[13], v[14], v[15], v[16], v[17], v[18],
--   v[19], v[20], v[21], v[22], v[23], v[24], v[25], v[26], v[27],
--   v[28], v[29], v[30], v[31], v[32], v[33], v[34], v[35], v[36],
--   v[37], v[38], v[39], v[40]
-- ] := by rcases v; simp_all; grind (splits := 100) (gen := 100) (ematch := 100)

end examples

end LeanZKCircuit
