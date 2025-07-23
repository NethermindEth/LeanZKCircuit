import Lean

namespace LeanZKCircuit

open Lean Meta

def warnExpected (e : Expr) (guard : Expr → MetaM Bool) (guardDescr : String)
                 (suggest : String := "") : MetaM Unit := do
  if !(←guard e) then logWarning m!"{guardDescr}. {e} : {← inferType e}.\n{suggest}"

def hasInstance (e : Expr) (inst : Name) (us : List Level := [.zero]) : MetaM Bool := do
  warnExpected e (inferType · <&> Expr.isType)
                 "Querying a typeclass of a non-sort expression"
                 "Did you mean to call `hasInstance` with `inferType e`?"
  if let .some _ ← trySynthInstance (.app (.const inst us) e) then return true
  return false

end LeanZKCircuit
