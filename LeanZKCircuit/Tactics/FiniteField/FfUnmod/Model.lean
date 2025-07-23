import Lean
import Qq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic

import LeanZKCircuit.Wheels

open Lean Meta Qq

namespace LeanZKCircuit

inductive OpT where | Add | Sub | Mul | Div deriving Repr, BEq, Inhabited

namespace OpT

def arity : OpT → ℕ
  | .Add | .Sub | .Mul | .Div => 2

def leanOp : OpT → Name
  | .Add => ``HAdd.hAdd
  | .Sub => ``HSub.hSub
  | .Mul => ``HMul.hMul
  | .Div => ``HDiv.hDiv

/--
  Maybe we can switch `OpT` to a class, I am trying to be as explicit as possible with everything
  to avoid difficult-to-diagnose meta errors.
-/
def allOps : Array OpT := #[.Add, .Sub, .Mul, .Div]

end OpT

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

/--
  Checks whether `e` is a `ZMod p` or `Fin p` for some prime `p`.

  We do not check `Field` and `Fintype` instances (cf. `isFFexpr`) because we often do not have
  the `Field` instance by default, e.g. for `Fin p`, even if we know `Nat.Prime p`.
-/
def knownField? (e : Expr) (p : Option ℕ := .none) : MetaM (Option FieldT) := do
  let (name, #[n]) := (← inferType e).getAppFnArgs | return .none
  let n : ℕ ← unsafe evalExpr _ q(ℕ) n
  if !isPrime n then return .none
  return (FieldT.ofName n name).filter <| p.elim (fun _ ↦ true) (fun p _ ↦ p == n)

/--
  Checks whether `e` is `OpT`. If `fT := .some T`, furthermore assume `OpT` is over `T`.

  - Note: Explicitly providing `fT` is also more efficient.
-/
def matchOpT? (e : Expr) (op : OpT) (fT : Option FieldT := .none) : MetaM (Option (Array Expr)) := do
  let .some fieldT ← fT.elim (knownField? e) (pure ∘ .some) | pure .none
  let mArgs ← (Array.range op.arity).mapM (fun _ ↦ mkFreshExprMVar fieldT.toExpr)
  return if ←isDefEq e (←mkAppM op.leanOp mArgs) then .some mArgs else .none

structure FFieldExpr where
  op : OpT
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
