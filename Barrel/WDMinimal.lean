import Barrel.Builtins
import Lean.Elab.BuiltinTerm

open Lean Meta Elab Term

namespace Barrel.WDMinimal

initialize registerTraceClass `barrel.wd.minimal

/-- A closed WD proof with only its used context, and the positions of those
parameters in the original statement's telescope. -/
structure Result where
  type : Expr
  proof : Expr
  keptBinders : Array Nat

/-- Recover the original full-context proof as an application of the minimal
constant. Recording the binder positions avoids a second proof search. -/
def Result.apply (result : Result) (fullType minimalConst : Expr) : MetaM Expr :=
  forallTelescope fullType fun binders _ => do
    let args := result.keptBinders.map (binders[·]!)
    mkLambdaFVars binders (mkAppN minimalConst args)

private def dependencyClosure (binders : Array Expr) (used : FVarIdSet) : MetaM FVarIdSet := do
  let mut used := used
  -- Local declarations are ordered by dependency, so one reverse pass suffices.
  for x in binders.reverse do
    if used.contains x.fvarId! then
      for id in (collectFVars {} (← inferType x)).fvarIds do
        used := used.insert id
  return used

private def usedPositions (binders : Array Expr) (used : FVarIdSet) : Array Nat :=
  binders.toList.zipIdx.toArray.filterMap fun (x, i) =>
    if used.contains x.fvarId! then some i else none

private def prune (type proof : Expr) : MetaM Result :=
  forallTelescope type fun binders conclusion => do
    let body := (mkAppN proof binders).headBeta
    let used ← dependencyClosure binders
      (collectFVars (collectFVars {} conclusion) body).fvarSet
    let keptBinders := usedPositions binders used
    let kept := keptBinders.map (binders[·]!)
    -- Keep the predicate as written, even when its definition erases an argument.
    -- This also keeps the predicate's head available to the reuse index.
    let proof ← mkLambdaFVars kept body
    let type ← mkForallFVars kept conclusion
    Meta.check proof
    unless ← isDefEq (← inferType proof) type do
      throwError "Pruned WD proof does not have its retained statement"
    return { type, proof, keptBinders }

private def relevantType (type : Expr) : MetaM (Expr × Array Nat) :=
  forallTelescope type fun binders conclusion => do
    -- Carrier types and instances occur in almost every hypothesis. They are kept
    -- through dependency closure, but do not make a hypothesis relevant by themselves.
    let targetVars := (collectFVars {} conclusion).fvarSet
    let roots ← binders.filterM fun x => do
      if !targetVars.contains x.fvarId! then return false
      let decl ← x.fvarId!.getDecl
      return !decl.binderInfo.isInstImplicit && !(← isProp decl.type) &&
        !(← whnf decl.type).isSort
    let mut used := targetVars
    for x in binders do
      let type ← inferType x
      if ← isProp type then
        let vars := (collectFVars {} type).fvarSet
        if roots.any (vars.contains ·.fvarId!) then
          used := used.insert x.fvarId!
    used ← dependencyClosure binders used
    let kept := usedPositions binders used
    let type ← mkForallFVars (kept.map (binders[·]!)) conclusion
    return (type, kept)

private def minimizeCore (type proof : Expr) : TermElabM Result := do
  let fallback ← prune type proof
  let saved ← saveState
  let improved ← tryCatchRuntimeEx
    (do
      let (candidate, positions) ← relevantType type
      let proof ← withLCtx {} #[] <| withoutErrToSorry do
        elabTermAndSynthesize (← `(term| by intros; open B.Builtins in b_wd))
          (some candidate)
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasFVar || proof.hasSorry then return none
      let result ← prune candidate proof
      if result.keptBinders.size < fallback.keptBinders.size then
        return some { result with keptBinders := result.keptBinders.map (positions[·]!) }
      return none)
    (fun ex => do
      trace[barrel.wd.minimal] "Bounded WD reproof stopped: {ex.toMessageData}"
      pure none)
  if let some result := improved then return result
  saved.restore
  return fallback

/-- Derive a dependency-pruned WD proof, trying the existing WD automation once in
 a relevance-filtered context first. The latter avoids retaining unrelated equalities
 introduced by substitution in the original proof. Failure keeps the pruned original.
 The whole attempt has its own bounded budget; a timeout or failure never invalidates
 the original proof, and no successful result contains `sorry`. -/
def minimize? (type proof : Expr) (maxHeartbeats : Nat := 2000) :
    TermElabM (Option Result) := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  if maxHeartbeats == 0 || type.hasMVar || proof.hasMVar || type.hasFVar ||
      proof.hasFVar || proof.hasSorry then return none
  let saved ← saveState
  withCurrHeartbeats do
    let start ← IO.getNumHeartbeats
    let ctx ← readThe Core.Context
    let limit := if ctx.maxHeartbeats == 0 then maxHeartbeats
      else min maxHeartbeats ((ctx.maxHeartbeats - (start - ctx.initHeartbeats)) / 1000)
    if limit == 0 then return none
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx =>
        { ctx with initHeartbeats := start, maxHeartbeats := limit * 1000
                   options := Lean.maxHeartbeats.set ctx.options limit }) do
        return some (← minimizeCore type proof))
      (fun ex => do
        saved.restore
        trace[barrel.wd.minimal] "Bounded WD minimization stopped: {ex.toMessageData}"
        pure none)

end Barrel.WDMinimal
