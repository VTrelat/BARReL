import Lean.Util.Trace
import POGReader.Extractor

open Lean

initialize registerTraceClass `barrel
initialize registerTraceClass `barrel.pog
initialize registerTraceClass `barrel.cache
initialize registerTraceClass `barrel.wd
initialize registerTraceClass `barrel.solve

register_option barrel.atelierb : String := {
  defValue := ""
  descr := "Path to the Atelier-B distribution"
}

register_option barrel.show_goal_names : Bool := {
  defValue := true
  descr := "Show the goal name on `obligation`"
}

register_option barrel.show_auto_solved : Bool := {
  defValue := false
  descr := "Show the number of goals that are automatically solved by `barrel_solve`"
}

register_option barrel.cache_dir : String := {
  defValue := ""
  descr := "Path to the cache directory for storing parsed POGs"
}

register_option barrel.progress : Bool := {
  defValue := true
  descr := "Show a live, self-updating progress card in the infoview for each `import` \
    (auto-solved / remaining counts, a progress bar, and the summary table once finished). \
    Set to false to suppress the panel and its reporting."
}

register_option barrel.summary : Bool := {
  defValue := false
  descr := "Log a summary table (solved/remaining counts, WD deduplication) as an info \
    message after an `import` finishes. The same table is always shown in the live progress \
    card; this option is for batch builds and logs."
}

namespace Barrel

/-- Settings owned by one B import; the import syntax derives its options from these fields. -/
structure ImportConfig where
  /-- Shared heartbeat budget for each WD equality/subsumption search; zero keeps exact hits. -/
  subsumeMaxHeartbeats : Nat := 400
  deriving Inhabited

/-- A translated obligation and its proof, retained in its import until `qed`. -/
structure Obligation where
  name : Name
  reason : String
  type : Expr
  isWd : Bool := false
  proof? : Option Expr := none
  auto : Bool := false
  position? : Option (Nat × Nat) := none
  progressIndex? : Option Nat := none
deriving Inhabited

/-- Cached selection and counts for an import's obligation array. -/
structure ObligationBookkeeping where
  byName : NameMap Nat := {}
  byDisplayName : Std.HashMap String Nat := {}
  nextPending : Nat := 0
  proven : Nat := 0
  autoProven : Nat := 0
  sorried : Nat := 0
  pending : Nat := 0

/-- A WD request handled by an earlier published theorem, without a new obligation. -/
structure WDReuseInfo where
  condition : Name
  theoremName : Name
  deriving Inhabited

/-- A proved adapter keeps the original WD statement without creating a proof obligation. -/
structure WDAdapter where
  name : Name
  type : Expr
  value : Expr

/-- Build the lookup and counts once, preserving the first occurrence of each name. -/
def ObligationBookkeeping.ofObligations (obligations : Array Obligation) :
    ObligationBookkeeping := Id.run do
  let mut result : ObligationBookkeeping := { nextPending := obligations.size }
  for i in [:obligations.size] do
    let obligation := obligations[i]!
    if !result.byName.contains obligation.name then
      result := { result with
        byName := result.byName.insert obligation.name i
        byDisplayName := result.byDisplayName.insert obligation.name.toString i }
    match obligation.proof? with
    | none =>
      result := { result with
        nextPending := min result.nextPending i, pending := result.pending + 1 }
    | some proof =>
      if proof.hasSorry then
        result := { result with sorried := result.sorried + 1 }
      else
        result := { result with
          proven := result.proven + 1
          autoProven := result.autoProven + if obligation.auto then 1 else 0 }
  return result

/-- An import owns a private environment branch extending `baseEnv`. -/
structure ImportContext where
  name : Name
  path : System.FilePath
  config : ImportConfig := {}
  baseEnv : Environment
  localEnv : Environment
  obligations : Array Obligation
  skipped : Array Name := #[]
  finalized : Bool := false
  wdUnique : Nat := 0
  wdAvoided : Nat := 0
  wdReuses : Array WDReuseInfo := #[]
  wdAdapters : Array WDAdapter := #[]
  bookkeeping : ObligationBookkeeping := .ofObligations obligations

/-- Rebuild the caches after replacing the whole obligation array. -/
def ImportContext.initializeBookkeeping (ctx : ImportContext) : ImportContext :=
  { ctx with bookkeeping := .ofObligations ctx.obligations }

/-- Select the first pending obligation in the stored WD-first order. -/
def ImportContext.nextObligation? (ctx : ImportContext) : Option Nat :=
  if ctx.bookkeeping.nextPending < ctx.obligations.size then
    some ctx.bookkeeping.nextPending
  else none

/-- Resolve a name relative to the selected import. -/
def ImportContext.findObligation? (ctx : ImportContext) (name : Name) : Option Nat :=
  ctx.bookkeeping.byName.find? (ctx.name ++ name)

/-- Test an exact dependency name without scanning unrelated obligations. -/
def ImportContext.isPendingName (ctx : ImportContext) (name : Name) : Bool :=
  (ctx.bookkeeping.byName.find? name).any fun i => ctx.obligations[i]!.proof?.isNone

/--
Store one successful proof and update its counts and next-pending cursor together. Invalid
indices and repeated proofs leave the original snapshot untouched and return `none`.
The cursor only moves forward, so skipped proved entries are scanned at most once over an
import's lifetime. Bulk obligation-array changes must rebuild the bookkeeping instead.
-/
def ImportContext.markProof? (ctx : ImportContext) (index : Nat) (proof : Expr)
    (position? : Option (Nat × Nat) := none) : Option ImportContext := do
  let obligation ← ctx.obligations[index]?
  guard obligation.proof?.isNone
  let obligations := ctx.obligations.set! index
    { obligation with proof? := some proof, position? }
  let mut nextPending := ctx.bookkeeping.nextPending
  while nextPending < obligations.size do
    if obligations[nextPending]!.proof?.isNone then break
    nextPending := nextPending + 1
  let hadSorry := proof.hasSorry
  let bookkeeping := { ctx.bookkeeping with
    nextPending
    pending := ctx.bookkeeping.pending - 1
    proven := ctx.bookkeeping.proven + if hadSorry then 0 else 1
    autoProven := ctx.bookkeeping.autoProven + if obligation.auto && !hadSorry then 1 else 0
    sorried := ctx.bookkeeping.sorried + if hadSorry then 1 else 0 }
  return { ctx with obligations, bookkeeping }

/-- Command snapshot state; importing another component does not replace earlier contexts. -/
structure DischargeState where
  contexts : NameMap ImportContext := {}
  latest? : Option Name := none
deriving Inhabited

/-- Import-local declarations and progress participate in Lean's command snapshot restoration. -/
initialize obligationContexts : EnvExtension DischargeState ←
  registerEnvExtension (pure {})

end Barrel
