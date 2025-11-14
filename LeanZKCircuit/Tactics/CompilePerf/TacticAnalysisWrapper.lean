import Lean
import Mathlib.Tactic

/-#
  Reformulates a bit of `Lean` and `TacticAnalysis` internels to allow for more flexibility.

  - We need `Tactic.run` to operate over `TacticM α` rather than `TacticM Unit`.
  - For `TacticAnalaysis`, we need `runPass` and `testTacticSeq` to not eat heartbeats.
-/

namespace LeanZKCircuit

open Lean

section

open Elab Tactic

/-
Code in this section is based on `Lean.Elab.Tactic`.
-/

@[inline]
private def runCore (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

@[inline]
private def runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> runCore x ctx s

def run (mvarId : MVarId) (x : TacticM α) : TermElabM (List MVarId × α) :=
  mvarId.withContext do
    let pendingMVarsSaved := (← get).pendingMVars
    modify fun s => { s with pendingMVars := [] }
    let aux : TacticM (List MVarId × α) := do
      let res ← x
      try
        (·, res) <$> getUnsolvedGoals
      catch ex =>
        if isAbortTacticException ex then
          (·, res) <$> getUnsolvedGoals
        else
          throw ex
    try
      runCore' aux { elaborator := .anonymous } { goals := [mvarId] }
    finally
      modify fun s => { s with pendingMVars := pendingMVarsSaved }

end

inductive SimpCtx where
  | simp (tkBegin tkEnd : Syntax) (args : Array Syntax) (loc : Option Syntax)
  | simpAll (tkBegin tkEnd : Syntax) (args : Array Syntax)
  deriving Repr

def SimpCtx.stxBegin : SimpCtx → Syntax
  | .simp tkBegin .. | .simpAll tkBegin .. => tkBegin

def SimpCtx.stxEnd : SimpCtx → Syntax
  | .simp _ tkEnd .. | .simpAll _ tkEnd .. => tkEnd

section

/-
Code in this section is based on `Mathlib.Tactic.TacticAnalysis`.
-/

open Meta Elab Tactic Command Mathlib.TacticAnalysis

def forceHeartbeats {α : Type} {m : Type → Type} [MonadWithReaderOf Core.Context m]
                    (heartBeats : ℕ) : m α → m α :=
  withTheReader Core.Context ({· with maxHeartbeats := heartBeats})

def testTacticSeq (config : ComplexConfig) (tacticSeq : Array (TSyntax `tactic))
                  (i : TacticNode) (ctx : config.ctx) :
    CommandElabM Unit := do
  withRef (mkNullNode tacticSeq) do
    let stx ← `(tactic| $tacticSeq;*)
    if let [goal] := i.tacI.goalsBefore then
      let (oldGoals, oldHeartbeats) ← withHeartbeats <|
        try
          -- The difference between `TacticAnalaysis.testTacticSeq` is that 
          -- we force the heartbeats option, as for some reason it is ignored.
          -- Note that we just reset `i.ctxI.options.getNat maxHeartbeats`, so in theory,
          -- `i.runTacticCode` should do it - but it does not.
          -- This may or may not have to do with the issues associated with `tryCatchRuntime`.
          (·.1) <$>
          i.ctxI.runTactic i.tacI goal fun goal ↦
            forceHeartbeats (i.ctxI.options.getNat `maxHeartbeats) (runTactic goal stx)
        catch e => do
          if !i.mayFail then
            logWarning m!"original tactic '{stx}' failed: {e.toMessageData}"
          return [goal]
      let (new, newHeartbeats) ← withHeartbeats <| config.test i.ctxI i.tacI ctx goal
      if let some msg ← config.tell stx oldGoals oldHeartbeats new newHeartbeats then
        logWarning msg

def runPass (config : ComplexConfig) (seq : Array TacticNode) :
    CommandElabM Unit := do
  let mut acc := none
  let mut firstInfo := none
  let mut tacticSeq := #[]
  for i in seq do
    if firstInfo.isNone then
      firstInfo := some i
    let stx : TSyntax `tactic := ⟨i.tacI.stx⟩
    tacticSeq := tacticSeq.push stx
    match config.trigger acc stx with
    | .continue ctx =>
      acc := ctx
    | .skip =>
      acc := none
      tacticSeq := #[]
      firstInfo := none
    | .accept ctx =>
      if let some i := firstInfo then
        -- The only difference between `TacticAnalysis.runPass` is that we call our local
        -- `testTactiSea`.
        testTacticSeq config tacticSeq i ctx
      else
        logWarningAt stx m!"internal error in tactic analysis: accepted an empty sequence."
      acc := none
  -- Insert a `done` at the end so we can handle a final `.continue` at the end.
  match config.trigger acc (← `(tactic| done)) with
  | .accept ctx =>
    if let some i := firstInfo then
      testTacticSeq config tacticSeq i ctx
  | _ => pure ()

end

end LeanZKCircuit
