import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.TacticAnalysis
import LeanZKCircuit.Tactics.CompilePerf.Options
import LeanZKCircuit.Tactics.CompilePerf.TacticAnalysisWrapper

open Lean Mathlib

namespace LeanZKCircuit

open Lean Parser Meta Elab Tactic in
def SimpCtx.stats (goal : MVarId) (ctx : SimpCtx)
                  (cinfo : ContextInfo) (tinfo : TacticInfo) :
  Command.CommandElabM (ℕ × TSyntax `tactic × Simp.Stats) := do
  let runInContext {α : Type} (x : TacticM α) : Command.CommandElabM α := do
    (·.1.2) <$> cinfo.runTactic tinfo goal fun goal ↦ run goal x |>.run
  match ctx with
  | .simp (loc := loc) (args := args) .. =>
    let ctxT : Array (TSyntax [``simpStar, ``simpErase, ``simpLemma]) := args.map (⟨·⟩)
    let (tac, loclen) ←
      match loc with
      | .none =>
        (·, 0) <$> `(tactic|simp [$ctxT,*])
      | .some loc =>
        (·, 1 + loc.getRange?.elim 0 Lean.Syntax.Range.bsize) <$> `(tactic|simp [$ctxT,*] $(⟨loc⟩))
    let l := loc.elim (.targets #[] true) expandLocation
    let {ctx, simprocs, dischargeWrapper,..} ← runInContext (mkSimpContext tac (eraseLocal := false))
    let simp ← runInContext (dischargeWrapper.with fun discharge? =>
                 goal.withContext do simpLocation ctx (simprocs := simprocs) discharge? l)
    return (loclen, tac, simp)
  | .simpAll (args := args) .. =>
    let ctxT : Array (TSyntax [``simpErase, ``simpLemma]) := args.map (⟨·⟩)
    dbg_trace s!"options: {cinfo.options}"
    let (tac, loclen) ← (·, 0) <$> `(tactic|simp_all [$ctxT,*])
    let { ctx, simprocs, .. } ← runInContext (
      (mkSimpContext tac (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true))
    )
    let x ← cinfo.runTactic tinfo goal fun goal ↦
      forceHeartbeats (cinfo.options.getNat `maxHeartbeats)
                      (Meta.simpAll goal ctx (simprocs := simprocs))
    return (loclen, tac, x.2)

open Lean Meta Elab Tactic in
@[tacticAnalysis linter.tacticAnalysis.optimise.compile_time.simpToSimpOnly,
  inherit_doc linter.tacticAnalysis.optimise.compile_time.simpToSimpOnly]
def Mathlib.TacticAnalysis.simpToSimpOnly : TacticAnalysis.Config where
  run seq := do
    runPass (seq := seq) {
    out := Unit
    ctx := SimpCtx
    trigger _ctx stx :=
      match stx with
      | `(tactic|simp%$tk [$args,*]%$tkend $loc:location) => .accept <| .simp tk tkend args loc
      | `(tactic|simp%$tk [$args,*]%$tkend) => .accept <| .simp tk tkend args .none
      | `(tactic|simp%$tk $loc:location) => .accept <| .simp tk tk #[] loc
      | `(tactic|simp%$tk) => .accept <| .simp tk tk #[] .none
      | `(tactic|simp_all%$tk [$args,*]%$tkend) => .accept <| .simpAll tk tkend args
      | `(tactic|simp_all%$tk) => .accept <| .simpAll tk tk #[]
      | _ => .skip
    test ci ti ctx goal := do
      dbg_trace "hello"
      let (loclen, tac, stats) ← ctx.stats goal ci ti
      for e in stats.usedTheorems.toArray do
        dbg_trace s!"e: {repr e}"
      let ((_, stx), _) ← ci.runTactic ti goal fun goal ↦ do
        run goal (mkSimpCallStx tac stats.usedTheorems) |>.run
      discard ∘ ci.runTactic ti goal fun goal ↦ do run goal (TryThis.addSuggestion ctx.stxBegin stx
        (origSpan? := do
          Syntax.ofRange ⟨(←ctx.stxBegin.getRange?).1, ⟨(←ctx.stxEnd.getRange?).2.1 + loclen⟩⟩)
        (header := "This compiles faster: ")) |>.run
    tell _stx _old _oldHeartbeats _new _newHeartbeats := .pure .none
  }

-- set_option maxHeartbeats 3450000

-- set_option linter.tacticAnalysis.optimise.compile_time.simpToSimpOnly true

-- theorem random_test_written_like_this_on_purpose {m n : ℕ} : m + n = n + m := by
--   induction' n with n ih
--   · simp
--   · rw [Nat.add_succ]
--     simp
--     skip
--     have : 0 + m + n = 0 + n + m := by sorry
--     simp at this
--     conv_rhs => rw [Nat.add_succ]
--     simp [Nat.succ_eq_add_one]
--     rw [add_assoc]
--     rewrite [add_comm (a := m)]
--     simp_all

end LeanZKCircuit
