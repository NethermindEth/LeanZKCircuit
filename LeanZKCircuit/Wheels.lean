import Mathlib.Data.Nat.Basic
import Batteries.Data.Nat.Basic

namespace LeanZKCircuit

def isPrime (n : ℕ) : Bool := Id.run do
  if n <= 1 then return false
  for i in [2:n.sqrt.succ] do
    if n % i == 0 then return false
  return true

end LeanZKCircuit
