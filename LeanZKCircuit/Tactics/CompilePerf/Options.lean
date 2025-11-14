import Lean

/--
Replace `simp` with the appropriate `simp only`.

NOTE: Can be generalised to anything that gives `<tac>?`.
-/
register_option linter.tacticAnalysis.optimise.compile_time.simpToSimpOnly : Bool := {
  defValue := false
}
