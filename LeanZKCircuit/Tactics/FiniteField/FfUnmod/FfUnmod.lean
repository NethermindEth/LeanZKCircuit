import Lean
import Qq
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Eval

import LeanZKCircuit.Wheels
import LeanZKCircuit.Tactics.Wheels
import LeanZKCircuit.Tactics.FiniteField.FfUnmod.Model

namespace LeanZKCircuit

namespace FFUnmod

open Qq Lean Meta Elab Term Tactic ArithT

/--
  Unfortunately, many standard `Field` types don't compute their cardinality.
  E.g. `Fintype.card (ZMod 3)` cannot be `evalExpr`'d to `3`.
  As such:
    `let cardinality ← unsafe evalExpr Nat q(Nat) (mkApp2 (.const ``Fintype.card [0]) eT inst) .unsafe`
  is currently clunky.

  Therefore, the current workaround is:
    `let cardinality ← isDefEq (mkApp2 (.const ``Fintype.card [0]) eT inst) q($p)`

  Sadly, this also is not ideal, because we run out of heartbeats quickly...

  - Do _not_ use this, it's not good enough.
-/
@[deprecated "Way too slow." (since := "Time immemorial.")]
def isFFexpr (e : Expr) (p : Option ℕ := .none) (trace := false) : MetaM Bool := do
  let eT ← inferType e
  let isField := ← hasInstance eT `Field [.zero]
  if trace then logInfo m!"{eT} is not `Field`."
  let .some inst ← trySynthInstance (.app (.const `Fintype [.zero]) eT) |
    if trace then logInfo m!"{eT} is not `Fintype`."
    return false
  match p with
  | .none => return isField
  | .some p =>
    if isNoncomputable (←getEnv) inst.getAppFn.constName!
    then
      logError m!"The instance {inst} is noncomputable, cannot enforce cardinality {p}."
      return false
    let cardinality ← isDefEq (mkApp2 (.const ``Fintype.card [0]) eT inst) q($p)
    return isField && cardinality

/--
  Returns `.some (opertion, type, unified arguments)` if the expression `e` is a recognised
  `operation` over a recognised finite field `type`.

  `unified arguments` are instantiated `MVars` of the arguments of the `operation`.
-/
def identifyArith? (e : Expr) : MetaM (Option FFieldExpr) := do
  let .some fieldT ← fieldOfArith? e | return .none
  for op in allOps do
    match ←matchArithT? e op fieldT with
    | .none => logInfo m!"{repr op} doesn't match"; continue
    | .some mvars => return .some ⟨op, fieldT, mvars⟩
  return .none

def rewriteLemmasOfArith (e : Expr) : MetaM (Array Name) := do
  let .some ffe@⟨op, t, args⟩ ← identifyArith? e | pure #[]
  logInfo m!"The expression: {e} is an operation: {repr op} over type: {repr t} with args: {args}"
  logInfo m!"Ready to rewrite with lemmas: {ffe.toRewriteLemmas}"
  return ffe.toRewriteLemmas

elab "ff_unmod" : tactic => do
  let x ← rewriteLemmasOfArith (←getMainTarget)
  logInfo m!"[ff_unmod] Rewriting with {x}."

notation "BB" => 2013265921

def x : Fin BB := 4
def y : Fin BB := 5
def z : Fin BB := 6

#eval rewriteLemmasOfArith (q(x + z))
#eval rewriteLemmasOfArith (q(x = z))
#eval rewriteLemmasOfArith (q(Add.add x z))
#eval rewriteLemmasOfArith (q(HAdd.hAdd x z))
#eval rewriteLemmasOfArith (q(Fin.add x z))

example : x + y := by
  ff_unmod

end FFUnmod

end LeanZKCircuit
