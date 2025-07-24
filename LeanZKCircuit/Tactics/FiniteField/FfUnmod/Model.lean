import Lean
import Qq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic

import LeanZKCircuit.Wheels

open Lean Meta Qq

namespace LeanZKCircuit

inductive ArithT where | Add | Sub | Mul | Div deriving Repr, BEq, Inhabited

namespace ArithT

def arity : ArithT → ℕ
  | .Add | .Sub | .Mul | .Div  => 2

def leanOp : ArithT → Name
  | .Add => ``HAdd.hAdd
  | .Sub => ``HSub.hSub
  | .Mul => ``HMul.hMul
  | .Div => ``HDiv.hDiv

/--
  Maybe we can switch `ArithT` to a class, I am trying to be as explicit as possible with everything
  to avoid difficult-to-diagnose meta errors.
-/
def allOps : Array ArithT := #[.Add, .Sub, .Mul, .Div]

end ArithT

inductive PropT where | Eq deriving Repr, BEq, Inhabited

namespace PropT

def arity : PropT → ℕ
  | .Eq => 2

def leanOp : PropT → Name
  | .Eq => ``_root_.Eq

def allOps : Array PropT := #[.Eq]

end PropT

inductive FieldT where | Fin (n : ℕ) | ZMod (n : ℕ) deriving Repr, BEq, Inhabited

namespace FieldT

def typeNames := #[``ZMod, ``Fin]

def ofName (n : ℕ) : Name → Option FieldT
  | ``_root_.Fin  => FieldT.Fin n
  | ``_root_.ZMod => FieldT.ZMod n
  | _             => .none

@[reducible]
def toExpr : FieldT → Expr
  | .Fin n => q(_root_.Fin $n)
  | .ZMod n => q(_root_.ZMod $n)

end FieldT

abbrev OpT := PropT ⊕ ArithT

/--
  Checks whether `e` is a `ZMod p` or `Fin p` for some prime `p`.

  We do not check `Field` and `Fintype` instances (cf. `isFFexpr`) because we often do not have
  the `Field` instance by default, e.g. for `Fin p`, even if we know `Nat.Prime p`.
-/
def fieldOfArith? (e : Expr) (p : Option ℕ := .none) : MetaM (Option FieldT) := do
  let (name, #[n]) := (← inferType e).getAppFnArgs | return .none
  let n : ℕ ← unsafe evalExpr _ q(ℕ) n
  if !isPrime n then return .none
  return (FieldT.ofName n name).filter <| p.elim (fun _ ↦ true) (fun p _ ↦ p == n)

/--
  Checks whether `e` is `ArithT`. If `fT := .some T`, furthermore assume `ArithT` is over `T`.

  - Note: Explicitly providing `fT` is also more efficient.
-/
def matchArithT? (e : Expr) (op : ArithT) (fT : Option FieldT := .none) : MetaM (Option (Array Expr)) := do
  let .some fieldT ← fT.elim (fieldOfArith? e) (pure ∘ .some) | pure .none
  let mArgs ← (Array.range op.arity).mapM (fun _ ↦ mkFreshExprMVar fieldT.toExpr)
  return if ←isDefEq e (←mkAppM op.leanOp mArgs) then .some mArgs else .none

-- /--
--   Checks whether `e` is `PropT`.
-- -/
-- def matchPropT? (e : Expr) : MetaM (Option (Array Expr)) := do
--   let (name, #[t, lhs, rhs]) := e.getAppFnArgs | return .none
--   logInfo m!"We have {name} for type {t} with lhs: {lhs} rhs: {rhs}"
--   pure .none

-- notation "BB" => 2013265921

-- def x : Fin BB := 4
-- def y : Fin BB := 5
-- def z : Fin BB := 6

-- #eval matchPropT? (q(x + z = 1))


structure FFieldExpr where
  op : ArithT
  type : FieldT
  args : Array Expr
  deriving Repr, BEq, Inhabited

namespace FFieldExpr

def toRewriteLemmas (e : FFieldExpr) : Array Name :=
  match e.type with
  | .ZMod _ => #[]
  | .Fin _ => match e.op with
              | .Add => #[``Fin.add_def]
              | .Sub => #[``Fin.sub_def]
              | .Mul => #[``Fin.mul_def]
              | .Div => #[]

end FFieldExpr

end LeanZKCircuit
