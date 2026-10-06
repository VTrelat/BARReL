import Lean.LabelAttribute
import Lean.Util.CollectAxioms
import Barrel.Subsume

open Lean Meta

register_option barrel.reuse_wd : Bool := {
  defValue := true
  descr := "Publish minimal WD theorems and reuse tagged facts from completed earlier imports"
}

namespace Barrel.WDReuse

/-- The conclusion head indexes facts independently of the particular WD operator. -/
def head? : Expr → Option Name
  | .forallE _ _ body _ => head? body
  | .mdata _ body => head? body
  | body => body.getAppFn.constName?

abbrev Index := NameMap (Array Name)

/-- A scoped, persistent index: additions survive module imports; erasure is supported. -/
initialize facts : SimpleScopedEnvExtension (Name × Name × Bool) Index ←
  registerSimpleScopedEnvExtension {
    name := `Barrel.WDReuse.facts
    initial := {}
    addEntry := fun index (head, name, enabled) =>
      let names := (index.find? head).getD #[]
      index.insert head (if !enabled then names.erase name
        else if names.contains name then names else names.push name)
  }

/-- Only ordinary, admission-free kernel theorems may enter the reuse index. -/
def add (name : Name) (kind := AttributeKind.global) : CoreM Unit := do
  let some (.thmInfo info) := (← getEnv).find? name
    | throwError "`barrel_wd` requires a theorem: `{name}`"
  if info.value.hasSorry || (← collectAxioms name).contains ``sorryAx then
    throwError "`barrel_wd` cannot register `{name}`: its proof depends on sorry"
  let some head := head? info.type
    | throwError "`barrel_wd` requires a theorem with a constant-headed conclusion"
  facts.add (head, name, true) kind

initialize registerBuiltinAttribute {
  name := `barrel_wd
  descr := "Kernel-checked WD theorems available to later BARReL imports"
  applicationTime := .afterCompilation
  add := fun name _ kind => add name kind
  erase := fun name => do
    let some info := (← getEnv).find? name | return
    let some head := head? info.type | return
    facts.add (head, name, false)
}

syntax (name := Lean.Parser.Attr.barrel_wd) "barrel_wd" : attr

def contains (env : Environment) (name : Name) : Bool := Id.run do
  let some info := env.find? name | return false
  let some head := head? info.type | return false
  return ((facts.getState env).find? head).any (·.contains name)

/-- Bound candidate collection and matching together, restoring scratch meta state. -/
def withBudget? (limit : Nat) (action : MetaM (Option α)) : MetaM (Option α) := do
  let start ← IO.getNumHeartbeats
  let ctx ← readThe Core.Context
  let remaining := if ctx.maxHeartbeats == 0 then limit
    else (ctx.maxHeartbeats - (start - ctx.initHeartbeats)) / 1000
  let limit := min limit remaining
  if limit == 0 then return none
  let saved ← saveState
  try
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx =>
        { ctx with
          initHeartbeats := start
          maxHeartbeats := limit * 1000
          options := barrel.subsume.maxHeartbeats.set (maxHeartbeats.set ctx.options limit) limit })
        action)
      (fun ex => do
        trace[barrel.subsume] "Bounded WD lookup stopped: {ex.toMessageData}"
        return none)
  finally
    saved.restore

/-- Search only the relevant bucket, under the encoder's existing cumulative search cap.
The supplied index is a snapshot taken before this import creates private declarations. -/
def findProof? (index : Index) (type : Expr) (limit : Nat) : MetaM (Option (Expr × Name)) := do
  if limit == 0 || !barrel.reuse_wd.get (← getOptions) then return none
  let some head := head? type | return none
  let names := (index.find? head).getD #[]
  if names.isEmpty then return none
  withBudget? limit do
    let mut candidates := #[]
    for name in names do
      Core.checkSystem "WD reuse"
      candidates := candidates.push (← mkConstWithFreshMVarLevels name)
    let some found ← Subsume.match? type candidates | return none
    let some name := found.candidate?.bind Expr.constName? | return none
    unless names.contains name do return none
    return some (found.proof, name)

end Barrel.WDReuse
