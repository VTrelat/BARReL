import Lean.Elab.Tactic
import Lean.LabelAttribute
import Lean.Util.ReplaceLevel

open Lean Meta Elab Tactic

register_option barrel.subsume.maxHeartbeats : Nat := {
  defValue := 2000
  descr := "Cumulative heartbeat budget for subsume, including candidate collection; 0 disables it"
}

initialize registerTraceClass `barrel.subsume

namespace Barrel.Subsume

inductive MatchKind where
  | defEq
  | subsumption
  deriving BEq

/-- A shared proof and the kind of matching that found it. -/
structure Match where
  proof : Expr
  kind : MatchKind

/-- Previously proved facts available to the bounded `subsume` tactic. -/
initialize lemmas : LabelExtension ←
  registerLabelAttr `subsume "Facts available to the bounded subsumption tactic"

syntax (name := Lean.Parser.Attr.subsume) "subsume" : attr

private partial def canon : Expr → Expr
  | .forallE _ t b bi => .forallE .anonymous (canon t) (canon b) bi
  | .lam _ t b bi => .lam .anonymous (canon t) (canon b) bi
  | .letE _ t v b nd => .letE .anonymous (canon t) (canon v) (canon b) nd
  | .app f a => .app (canon f) (canon a)
  | .mdata _ e => canon e
  | .proj n i e => .proj n i (canon e)
  | e => e

private partial def rigidShape? (env : Environment) (type : Expr) (arity := 0) :
    Option (Nat × Name) :=
  match type with
  | .forallE _ _ body _ => rigidShape? env body (arity + 1)
  | .mdata _ body => rigidShape? env body arity
  | _ => do
    let .const name _ := type.getAppFn | none
    guard (← env.find? name).isInductive
    return (arity, name)

-- Runtime timeouts propagate to the one outer budget handler; a failed comparison restores
-- scratch assignments before another witness is considered.
private def tryDefEq (a b : Expr) : MetaM Bool := do
  let saved ← saveState
  try
    if ← isDefEq a b then return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

-- A supplied polymorphic constant may have fresh unresolved universe arguments. Instantiate
-- those locally, without assigning metavariables belonging to the surrounding proof.
private def freshCandidate (candidate : Expr) : MetaM Expr := do
  let candidate ← instantiateMVars candidate
  if !candidate.isConst then return candidate
  let mut levels : Std.HashMap LMVarId Level := {}
  for id in (collectLevelMVars {} candidate).result do
    levels := levels.insert id (← mkFreshLevelMVar)
  return candidate.replaceLevel fun level => do
    let .mvar id := level | none
    levels[id]?

private def noScratchVariables (proof : Expr) : MetaM Bool := do
  let depth := (← getMCtx).depth
  for id in ← getMVars proof do
    if (← id.getDecl).depth >= depth then return false
  for id in (collectLevelMVars {} proof).result do
    if (← getMCtx).lDecls.find? id |>.any (·.depth >= depth) then return false
  return true

private def matchDefEq? (target candidate : Expr) : MetaM (Option Match) := withNewMCtxDepth do
  let candidate ← freshCandidate candidate
  let type ← inferType candidate
  let env ← getEnv
  let shape := rigidShape? env target
  let earlierShape := rigidShape? env type
  if let some requested := shape then
    if let some earlier := earlierShape then
      if earlier != requested then return none
  unless ← tryDefEq type target do return none
  let proof ← instantiateMVars candidate
  unless ← noScratchVariables proof do return none
  return some { proof, kind := .defEq }

-- Whole-type equality has already been tried for every supplied candidate.
private def subsumeCandidate? (target : Expr) (binders witnesses : Array Expr)
    (conclusion candidate : Expr) : MetaM (Option Match) := withNewMCtxDepth do
  let candidate ← freshCandidate candidate
  let type ← inferType candidate
  let env ← getEnv
  let shape := rigidShape? env target
  let earlierShape := rigidShape? env type
  if let some requested := shape then
    if let some earlier := earlierShape then
      if earlier.2 != requested.2 then return none
  let (args, _, result) ← forallMetaTelescopeReducing type
  unless ← tryDefEq result conclusion do return none
  for arg in args do
    Core.checkSystem "subsume"
    if ← arg.mvarId!.isAssigned then continue
    let domain ← instantiateMVars (← inferType arg)
    let isHyp ← isProp domain
    let name := (← arg.mvarId!.getDecl).userName
    let preferred ← witnesses.filterM fun x => do
      return !isHyp && (← x.fvarId!.getDecl).userName == name
    let choices := preferred ++ witnesses.filter (!preferred.contains ·)
    let mut found := false
    for exact in [true, false] do
      for x in choices do
        Core.checkSystem "subsume"
        let type ← instantiateMVars (← inferType x)
        let matched ← if exact then pure (canon type == canon domain)
                       else tryDefEq type domain
        if matched then
          arg.mvarId!.assign x
          found := true
          break
      if found then break
    unless found do return none
  let proof ← instantiateMVars (← mkLambdaFVars binders (mkAppN candidate args))
  unless ← noScratchVariables proof do return none
  Meta.check proof
  unless ← tryDefEq (← inferType proof) target do return none
  return some { proof, kind := .subsumption }

private def search? (target : Expr) (candidates : Array Expr) : MetaM (Option Match) := do
  -- Prefer an existing proof directly, before opening binders or trying specialization.
  -- Both phases run inside the same outer budget and rollback scope.
  for candidate in candidates do
    Core.checkSystem "subsume"
    let result ← try matchDefEq? target candidate catch _ => pure none
    if let some found := result then
      trace[barrel.subsume] "Reused definitionally equal proof candidate: {candidate}"
      return some found
  let ambient := (← getLCtx).getFVars
  forallTelescopeReducing target fun binders conclusion => do
    let witnesses := ambient ++ binders
    let boundProofs ← binders.filterM fun x => do isProp (← inferType x)
    let candidates := boundProofs ++ candidates
    for candidate in candidates do
      Core.checkSystem "subsume"
      let result ← try subsumeCandidate? target binders witnesses conclusion candidate
        catch _ => pure none
      if let some found := result then
        trace[barrel.subsume] "Reused proof candidate: {candidate}"
        return some found
    return none

private def budget : CoreM (Nat × Nat) := do
  let now ← IO.getNumHeartbeats
  let ctx ← read
  let configured := barrel.subsume.maxHeartbeats.get ctx.options
  let remaining := if ctx.maxHeartbeats == 0 then configured
    else (ctx.maxHeartbeats - (now - ctx.initHeartbeats)) / 1000
  return (now, min configured remaining)

private def cappedContext (ctx : Core.Context) (start limit : Nat) : Core.Context :=
  { ctx with initHeartbeats := start, maxHeartbeats := limit * 1000
             options := maxHeartbeats.set ctx.options limit }

/-- Try definitional equality across candidates before specialization and hypothesis weakening.
The entire search has one bounded budget. Existing metavariables are frozen; temporary
matching variables are instantiated before returning, and the original meta state is restored. -/
def match? (target : Expr) (candidates : Array Expr) : MetaM (Option Match) := do
  let (start, limit) ← budget
  if limit == 0 then return none
  let saved ← saveState
  try
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => cappedContext ctx start limit) <|
        search? target candidates)
      (fun ex => do
        trace[barrel.subsume] "Bounded proof search stopped: {ex.toMessageData}"
        pure none)
  finally
    saved.restore

/-- Return the proof found by the combined, bounded matching search. -/
def prove? (target : Expr) (candidates : Array Expr) : MetaM (Option Expr) := do
  return (← match? target candidates).map (·.proof)

private def evalSubsume (terms : Array Syntax) : TacticM Unit := withMainContext do
  let (start, limit) ← budget
  if limit == 0 then throwError "`subsume` is disabled or its heartbeat budget is exhausted"
  let saved ← saveState
  let solved ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => cappedContext ctx start limit) do
      let mut candidates := #[]
      for term in terms do
        Core.checkSystem "subsume"
        candidates := candidates.push (← elabTermForApply term (mayPostpone := false))
      for decl in ← getLCtx do
        Core.checkSystem "subsume"
        if !decl.isImplementationDetail && (← isProp decl.type) then
          candidates := candidates.push decl.toExpr
      for name in lemmas.getState (← getEnv) do
        Core.checkSystem "subsume"
        candidates := candidates.push (← mkConstWithFreshMVarLevels name)
      let some proof ← prove? (← getMainTarget) candidates | return false
      unless ← (← getMainGoal).checkedAssign proof do return false
      replaceMainGoal []
      return true)
    (fun ex => do
      trace[barrel.subsume] "Bounded tactic stopped: {ex.toMessageData}"
      pure false)
  if solved then return
  saved.restore
  throwError "`subsume` found no proof within its heartbeat budget"

syntax (name := subsume) "subsume" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| subsume) => evalSubsume #[]
  | `(tactic| subsume [$terms,*]) => evalSubsume terms.getElems

end Barrel.Subsume
