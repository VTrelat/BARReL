import Lean.Meta.Match.MatcherInfo
import Lean.ReducibilityAttrs
import Lean.DocString
import Lean.Compiler.InlineAttrs
import Barrel.Meta
import Barrel.EnvironmentIdentity
import Barrel.Subsume
import Barrel.WDReuse

open Lean

namespace Barrel

private def sameDeclaration : ConstantInfo → ConstantInfo → Bool
  | .thmInfo a, .thmInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .axiomInfo a, .axiomInfo b => a == b
  | _, _ => false

private partial def registerPrefixes (env : Environment) : Name → Environment
  | .str p s =>
    if s.startsWith "_" then env else registerPrefixes (env.registerNamespace p) p
  | _ => env

/--
Copy metadata that ordinary declaration replay does not expose on the destination branch.
In particular, matchers need their `MatcherInfo` to remain usable by `split` and simplification.
-/
private def copyDeclarationMetadata (source : Environment) (names : Array Name) : CoreM Unit := do
  let subsumeLemmas := Subsume.lemmas.getState source
  for name in names do
    modifyEnv fun env => registerPrefixes env name
    if let some info := Meta.Match.Extension.getMatcherInfo? source name then
      Meta.Match.addMatcherInfo name info
    if let some doc := docStringExt.find? source name then
      modifyEnv fun env => docStringExt.insert env name doc
    if let some ranges := declRangeExt.find? source name then
      addDeclarationRanges name ranges
    if subsumeLemmas.contains name then
      Subsume.lemmas.add name
    if WDReuse.contains source name then
      WDReuse.add name
    setReducibilityStatus name (getReducibilityStatusCore source name)
    if let some attr := Compiler.getInlineAttribute? source name then
      setEnv (← ofExcept <| Compiler.setInlineAttribute (← getEnv) name attr)
  -- Realization contexts must capture the complete merged metadata, not a partial prefix.
  for name in names do
    if source.areRealizationsEnabledForConst name then
      setEnv (← (← getEnv).enableRealizationsForConst (← getOptions) name)

/--
Rebase the declarations added between `base` and `localEnv` onto `current`, checking collisions
and kernel results before returning the merged environment. The caller must retain the prefix
invariant: `localEnv` is obtained by successfully extending `base` with synchronous kernel
checking. Failed elaborations must be rolled back before storing a context. The global branch may
contain arbitrary new declarations, including inductive types. This action does not modify its caller's environment.
-/
def mergeContext (base localEnv current : Environment) : CoreM Environment := do
  let baseChecked := base.toKernelEnv
  let sourceChecked := localEnv.toKernelEnv
  let delta := sourceChecked.constants.map₂.toList.filter fun (name, _) =>
    !baseChecked.constants.contains name
  let mut names := #[]
  for (name, checked) in delta do
    let some info := (localEnv.setExporting false).find? name
      | throwError "BARReL declaration `{name}` is missing from its local environment."
    if current.containsOnBranch name then
      throwError "Cannot publish BARReL declaration `{name}`: that name is already declared."
    match info with
    | .thmInfo _ | .defnInfo _ | .axiomInfo _ => pure ()
    | _ =>
      throwError "Cannot merge BARReL helper `{name}`: unsupported declaration kind."
    unless sameDeclaration info checked do
      throwError "BARReL declaration `{name}` differs from its kernel-checked declaration."
    names := names.push name
  let merged ← current.replayConsts base localEnv
  -- Lean's replay silently drops a failed kernel replay. Check the authoritative kernel map
  -- before accepting its elaborator-facing constant map or updating any import state.
  let mergedChecked := merged.toKernelEnv
  for (name, info) in delta do
    let some checked := mergedChecked.find? name
      | throwError "Kernel checking failed while merging BARReL declaration `{name}`."
    unless sameDeclaration info checked do
      throwError "Kernel checking changed BARReL declaration `{name}` while merging."
  withEnv merged do
    copyDeclarationMetadata localEnv names
    getEnv

/-- Ignore only BARReL's own command-state extension when checking external changes. -/
def sameExternalEnvironment (a b : Environment) : BaseIO Bool :=
  sameEnvironmentExcept obligationContexts.idx a b

/-- Keep the checked local branch when only BARReL bookkeeping changed; otherwise rebase. -/
def workingEnvironment (ctx : ImportContext) (current : Environment) : CoreM Environment := do
  if ← sameExternalEnvironment ctx.baseEnv current then
    trace[barrel.cache] "Reusing local environment for {ctx.name}"
    -- Other imported contexts may have progressed since this branch was last used.
    return obligationContexts.setState ctx.localEnv (obligationContexts.getState current)
  trace[barrel.cache] "Replaying local environment for {ctx.name}"
  mergeContext ctx.baseEnv ctx.localEnv current

end Barrel
