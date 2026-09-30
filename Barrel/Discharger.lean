import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import Barrel.Encoder
import POGReader.Basic
import Barrel.Context
import Barrel.Tactics
import Barrel.Progress

open Lean Elab Term Command

private structure ParserResult where
  path : System.FilePath
  name : String
  goals : Array B.POG.Goal

private def nameOf (mchPath : System.FilePath) : String :=
  mchPath.fileStem.get!

/-- Operation-group name for a POG goal, used to cluster the per-obligation map cells: the
    part before `_step_` (e.g. `Operation_step_6` ↦ `Operation`), else the whole name. -/
private def deriveOp (name : String) : String :=
  match name.splitOn "_step_" with
  | x :: _ :: _ => x
  | _ => name

private def pog2goals (name : String) (pogPath : System.FilePath) (mchPath : Option System.FilePath := .none) : CommandElabM ParserResult := do
  let pog : String ← IO.FS.readFile pogPath
  let goals ← B.POG.extractGoals <$> B.POG.parse' pog

  return {
    path := match mchPath with | .some p => p | .none => pogPath
    name
    goals
  }

private def mch2goals (name : String) (dir mchPath : System.FilePath) : CommandElabM ParserResult := do
  let atelierBDir := System.FilePath.mk <| barrel.atelierb.get (← getOptions)

  let mchName := nameOf mchPath

  -- Parse the machine, generate the POG
  let stdout ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"bxml").toString
    args := #["-I", dir.toString, "-a", mchPath.toString]
  }
  let cacheDir := barrel.cache_dir.get (← getOptions)
  let tmp ← do
    if cacheDir.isEmpty then
      IO.FS.createDirAll (dir/".barrel")
      pure <| dir/".barrel"
    else if ←System.FilePath.pathExists (System.FilePath.mk cacheDir) then
      pure (System.FilePath.mk cacheDir)
    else
      IO.FS.createDirAll (System.FilePath.mk cacheDir)
      pure (System.FilePath.mk cacheDir)
  let bxml := tmp/System.FilePath.addExtension mchName "bxml"
  IO.FS.writeFile bxml stdout
  let _ ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"pog").toString
    /-
      Although `pog` can generate the WD conditions for us (with the `-w` flag), we will not be using these.

      Reasons are:
      * The WD conditions are placed at the very end of the `.pog` file, while we would need to
        reference this in our main goals.
      * Knowing whether a goal is a WD condition requires parsing its description, which is very
        fragile and error-prone.
      * Even with these issues ironed out, we would still need complicated logic in order to correctly
        instantiate those conditions in our goals (which is even worse in the cases where a WD condition
        may depend on the previous conjunct, e.g. in goals like `∃ G. G ∈ A ⟶ B ∧ G(x) ∈ B`, where the
        generated WD condition is `∀ G. G ∈ A ⟶ B ⇒ x ∈ dom(G) ∧ G ∈ dom(G) ⇸ ran(G)`).
    -/
    args := #["-p", (atelierBDir/"include"/"pog"/"paramGOPSoftware.xsl").toString, /- "-w", -/ bxml.toString]
  }

  -- Then parse the POG and generate the goals
  pog2goals name (mchPath := mchPath) <| bxml.withExtension "pog"

private def pog2obligations (res : ParserResult) (contextName : Name) :
    CommandElabM (Array Barrel.Obligation × Array Name) := liftTermElabM do
  let ⟨_, name, goals⟩ := res

  let t0 ← IO.monoMsNow
  let nbPOs := goals.size
  let progress := (← getOptions).getBool `barrel.progress true

  let mut res : Array Barrel.Obligation := #[]
  let mut wds : Array Barrel.Obligation := #[]
  -- The whole import shares one metavariable context. Encoder cache hits reuse the
  -- original closed proof metavariable, including when its obligation is still pending.
  let mut encoder : B.Encoder.State := {}
  -- Auto-discharge splits its successes into really-proven (green) and sorried (yellow, a
  -- `barrel_solve` alternative can close a genuinely-`sorry` goal with `sorry`); their sum is
  -- the "auto-solved" count.
  let mut autoProven := 0
  let mut autoSorried := 0
  let mut nbGoals := goals.size
  let mut i := 0

  let mut skipped : Array Name := #[]

  -- Per-obligation map for the progress card: one `{d, n, op, st, line, char}` entry per
  -- subgoal, filled as each is auto-discharged or left pending. `nsPrefix` trims the
  -- namespace/machine prefix off declNames for a compact cell label.
  let nsPrefix := contextName.toString ++ "."
  let mut obligations : Array Json := #[]

  if progress then
    -- Evict any stale `importing` card left by a previous elaboration (e.g. the user changed
    -- the imported file before its import finished), then post this import's fresh card.
    Barrel.Progress.dropImporting
    Barrel.Progress.report name nbGoals 0 nbPOs 0 0 true 0

  for g in goals do
    let declName := contextName.str s!"{g.name}_{i}"

    -- Encoding runs with its own heartbeat budget and its failures (unsupported construct,
    -- ill-typed translation, timeout) are confined to this obligation: on large industrial
    -- POGs a single unencodable goal must not abort the import of the thousands of others.
    let enc? ← withCurrHeartbeats <| withOptions (Elab.async.set · false) do
      let saved ← saveState
      tryCatchRuntimeEx (do
        pure <| some (← g.toExpr declName encoder))
        fun ex => do
          saved.restore
          logWarning m!"Failed to encode proof obligation `{declName}` ({g.reason}), skipping it:{indentD ex.toMessageData}"
          pure none

    let some (g', newWDs, encoder') := enc?
      | skipped := skipped.push declName
        nbGoals := nbGoals - 1
        i := i + 1
        continue
    encoder := encoder'
    let wds' := newWDs.map fun (n, e) => (n, "Assertion is well-defined", e, true)
    let opName := deriveOp g.name

    nbGoals := nbGoals + wds'.size
    let try_discharge := wds'.push (declName, g.reason, g', false)

    -- NOTE: Now try and solve it automatically...if possible
    for (declName, reason, g, isWd) in try_discharge do
      -- `withCurrHeartbeats` gives every subgoal its own full heartbeat budget, and
      -- `tryCatchRuntimeEx` is required because a heartbeat/recursion-depth timeout is a
      -- *runtime* exception, which an ordinary `try … catch` re-throws: without it a single
      -- diverging `barrel_solve` attempt aborts the whole `import` command instead of just
      -- leaving its obligation to the user.
      let (gOrWd, _hb) ← withCurrHeartbeats <| withOptions (Elab.async.set · false) do
        let hb₀ ← IO.getNumHeartbeats
        let saved ← saveState
        let r : _ ⊕ _ ← tryCatchRuntimeEx
          (do
            -- TODO: we should split on `isWd` to apply relevant tactics
            trace[barrel.solve] m!"Trying to solve theorem {declName} (isWd: {isWd}):{indentExpr g}"
            let e ← withDeclName declName <| withoutErrToSorry do
              Meta.check g
              instantiateMVars =<< elabTermAndSynthesize (← `(term| by barrel_solve)) (.some g)

            trace[barrel.solve] m!"{Lean.checkEmoji} Success! (spent {((← IO.getNumHeartbeats) - hb₀) / 1000} heartbeats)"

            let levelParams := (collectLevelParams (collectLevelParams {} g) e).params

            let decl : Declaration := .thmDecl {
              name := declName
              levelParams := levelParams.toList
              type := g
              value := e
            }

            ensureNoUnassignedMVars decl
            if (← getThe Core.State).messages.hasErrors then
              throwError "Automatic proof reported errors"
            addDecl decl false

            Lean.addDocStringOf false declName .missing
              (mkNode ``Parser.Command.docComment #[
                mkAtom "/--",
                mkAtom s!"Machine `{name}`, proof obligation `{declName}`: {reason} -/"
              ])

            pure <| .inl e)
          fun ex => do
            saved.restore
            trace[barrel.solve] m!"{Lean.crossEmoji} Failed! (spent {((← IO.getNumHeartbeats) - hb₀) / 1000} heartbeats)\n{ex.toMessageData}"

            pure <| .inr (declName, reason, g, isWd)
        pure (r, ((← IO.getNumHeartbeats) - hb₀) / 1000)

      let proof? := match gOrWd with
        | .inl e => some e
        | .inr _ => none
      if let some e := proof? then
        if e.hasSorry then autoSorried := autoSorried + 1 else autoProven := autoProven + 1
      let goal : Barrel.Obligation := {
        name := declName, reason, type := g, isWd, proof?, auto := proof?.isSome
        progressIndex? := some obligations.size }
      if isWd then wds := wds.push goal else res := res.push goal

      -- Record this subgoal's cell: green (auto), yellow (auto-sorry) or neutral (pending,
      -- to be filled by an `obligation` command). Matched back by `d` (the declName) at replay.
      let dnStr := declName.toString
      let short := if dnStr.startsWith nsPrefix then (dnStr.drop nsPrefix.length).toString else dnStr
      let stStr := match gOrWd with
        | .inl e => if e.hasSorry then "sorry" else "auto"
        | .inr _ => "pending"
      obligations := obligations.push <| Json.mkObj [
        ("d", .str dnStr), ("n", .str short),
        ("op", .str opName), ("st", .str stStr), ("line", .null), ("char", .null)]

      if progress then
        let elapsed := (← IO.monoMsNow) - t0
        Barrel.Progress.report name nbGoals (i + 1) nbPOs autoProven autoSorried true elapsed

    i := i + 1

  let goals := wds ++ res
  let dt := (← IO.monoMsNow) - t0
  let autoDischarged := autoProven + autoSorried

  let wdDistinct := nbGoals - (nbPOs - skipped.size)
  let pct := if nbGoals == 0 then 0 else autoDischarged * 1000 / nbGoals
  let rows : Array (String × String) := #[
    ("auto-solved", s!"{autoDischarged} / {nbGoals} ({pct / 10}.{pct % 10}%)"),
    ("WD goals", s!"{wdDistinct} unique ({encoder.hits} allocations avoided)"),
    ("remaining", s!"{goals.filter (·.proof?.isNone) |>.size}"),
    ("import time", s!"{dt / 1000}.{dt % 1000 / 100} s")
  ]
  if progress then
    Barrel.Progress.report name nbGoals nbPOs nbPOs autoProven autoSorried false dt
      (summary := Json.arr <| rows.map λ (l, v) ↦ Json.arr #[.str l, .str v])
      (obligations := obligations)

  if !skipped.isEmpty then
    logWarning s!"Skipped {skipped.size} proof obligations that could not be encoded; `qed` will refuse this import."
  if (← getOptions).getBool `barrel.show_auto_solved && autoDischarged > 0 then
    logInfo s!"🎉 Automatically solved {autoDischarged} out of {nbGoals} subgoals!"

  -- The same table also lands in the live progress card; this text rendering is for
  -- batch builds and plain-diagnostics setups.
  if (← getOptions).getBool `barrel.summary false then
    let w₁ := rows.foldl (λ m r ↦ max m r.1.length) 0
    let w₂ := rows.foldl (λ m r ↦ max m r.2.length) 0
    let pad := λ (s : String) (w : Nat) ↦ s.pushn ' ' (w - s.length)
    let hbar := λ (l m r : String) ↦ l ++ "".pushn '─' (w₁ + 2) ++ m ++ "".pushn '─' (w₂ + 2) ++ r
    let mut lines := #[s!"Import summary — `{name}`", hbar "┌" "┬" "┐"]
    for (l, r) in rows do
      lines := lines.push s!"│ {pad l w₁} │ {pad r w₂} │"
    lines := lines.push (hbar "└" "┴" "┘")
    logInfo <| "\n".intercalate lines.toList

  return (goals, skipped)

/-- Resolve an explicit import in the current namespace, or the latest imported context. -/
private def resolveContext (id? : Option (TSyntax `ident)) : CommandElabM Barrel.ImportContext := do
  let state := Barrel.obligationContexts.getState (← getEnv)
  let name ← match id? with
    | none =>
      match state.latest? with
      | some name => pure name
      | none => throwError "No B machine or POG has been imported."
    | some id => do
      let name := id.getId.eraseMacroScopes
      let mut ns ← getCurrNamespace
      repeat
        let candidate := ns ++ name
        if state.contexts.contains candidate then break
        if ns.isAnonymous then
          throwErrorAt id "Machine or POG `{name}` not found. Import it first."
        ns := ns.getPrefix
      pure (ns ++ name)
  let some ctx := state.contexts.find? name | throwError "Import context `{name}` not found."
  return ctx

private def saveContext (ctx : Barrel.ImportContext) (latest := false) : CommandElabM Unit :=
  modifyEnv (Barrel.obligationContexts.modifyState · fun state =>
    { state with contexts := state.contexts.insert ctx.name ctx
                 latest? := if latest then some ctx.name else state.latest? })

private def ensureOpen (ctx : Barrel.ImportContext) : CommandElabM Unit := do
  if ctx.finalized then
    throwError "Import `{ctx.name}` has already been finalized by `qed`."

private def reportContext (ctx : Barrel.ImportContext) : CommandElabM Unit := do
  if barrel.progress.get (← getOptions) then
    Barrel.Progress.reportProof ctx.name.toString ctx.bookkeeping.proven ctx.bookkeeping.sorried
    Barrel.Progress.reportActive ctx.name.toString false

private def findObligation (ctx : Barrel.ImportContext) (id? : Option (TSyntax `ident)) :
    CommandElabM Nat := do
  match id? with
  | none =>
    let some i := ctx.nextObligation?
      | throwError "There are no more obligations to discharge for `{ctx.name}`."
    return i
  | some id =>
    let name := id.getId.eraseMacroScopes
    let some i := ctx.findObligation? name
      | throwErrorAt id "Obligation `{name}` not found in `{ctx.name}`."
    if ctx.obligations[i]!.proof?.isSome then
      throwErrorAt id "Obligation `{ctx.obligations[i]!.name}` is already proved."
    return i

private def withContextProgress (ctx : Barrel.ImportContext) (action : CommandElabM Unit) :
    CommandElabM Unit := do
  let progress := barrel.progress.get (← getOptions)
  if progress then Barrel.Progress.reportActive ctx.name.toString true
  try
    action
  catch ex =>
    if progress then Barrel.Progress.reportError ctx.name.toString
    throw ex
  finally
    if progress then Barrel.Progress.reportActive ctx.name.toString false

private def proveObligation (ctx : Barrel.ImportContext) (id? : Option (TSyntax `ident))
    (proof : Term) (ref : Syntax) : CommandElabM Unit := withContextProgress ctx do
  ensureOpen ctx
  let i ← findObligation ctx id?
  let obligation := ctx.obligations[i]!
  let global ← getEnv
  let ((value, position), localEnv) ← withoutModifyingEnv' do
    setEnv (← liftCoreM <| Barrel.workingEnvironment ctx global)
    -- A WD theorem must exist before Lean can check a type referring to its constant.
    let missing := obligation.type.getUsedConstants.filter ctx.isPendingName
    unless missing.isEmpty do
      throwErrorAt ref "Obligation `{obligation.name}` depends on unproved obligations: {missing.toList}. Prove them first."
    if barrel.show_goal_names.get (← getOptions) then
      logInfoAt ref m!"{obligation.name}: {obligation.reason}"
    let value ← liftTermElabM <| withCurrHeartbeats <|
        withOptions (Elab.async.set · false) <| withoutErrToSorry <|
        withDeclName obligation.name do
      Meta.check obligation.type
      let value ← elabTermAndSynthesize proof (some obligation.type)
      let value ← instantiateMVars value
      -- Explicit `sorry` remains a Lean admission; tactic errors must never advance the queue.
      if (← getThe Core.State).messages.hasErrors then
        throwError "Proof of `{obligation.name}` reported errors; obligation remains unproved."
      let params := collectLevelParams (collectLevelParams {} obligation.type) value
      let decl := Declaration.thmDecl {
        name := obligation.name, levelParams := params.params.toList,
        type := obligation.type, value }
      ensureNoUnassignedMVars decl
      addDecl decl
      Lean.addDocStringOf false obligation.name .missing
        (mkNode ``Parser.Command.docComment #[mkAtom "/--",
          mkAtom s!"Machine `{ctx.name}`, proof obligation `{obligation.name}`: {obligation.reason} -/"])
      return value
    let fm ← getFileMap
    let position := ref.getPos?.map fun p =>
      let pos := fm.toPosition p
      (pos.line - 1, pos.column)
    pure (value, position)
  let some ctx := ctx.markProof? i value position
    | throwError "Obligation `{obligation.name}` is no longer pending."
  let ctx := { ctx with baseEnv := global, localEnv }
  saveContext ctx
  if barrel.progress.get (← getOptions) then
    let (line, char) := position.getD (0, 0)
    Barrel.Progress.reportObligation ctx.name.toString obligation.name.toString
      (if value.hasSorry then "sorry" else "hand") line char obligation.progressIndex?
  reportContext ctx

private def finalizeContext (ctx : Barrel.ImportContext) : CommandElabM Unit :=
    withContextProgress ctx do
  ensureOpen ctx
  if ctx.bookkeeping.pending != 0 || !ctx.skipped.isEmpty then
    let names := ctx.obligations.filterMap fun ob => if ob.proof?.isNone then some ob.name else none
    throwError "Cannot finalize `{ctx.name}`: {ctx.bookkeeping.pending} unproved obligations {names.toList}; {ctx.skipped.size} unencoded obligations {ctx.skipped.toList}."
  -- Merge onto the current environment, preserving declarations added since the import.
  -- Nothing is published until the entire merge has passed kernel verification.
  let env ← liftCoreM <| Barrel.mergeContext ctx.baseEnv ctx.localEnv (← getEnv)
  setEnv env
  saveContext { ctx with finalized := true }
  reportContext ctx

declare_syntax_cat import_kind
syntax "machine" : import_kind
syntax "system" : import_kind
syntax "pog" : import_kind
syntax "refinement" : import_kind
syntax "implementation" : import_kind

private def extFromKind : TSyntax `import_kind → MacroM String
  | `(import_kind| machine) => pure "mch"
  | `(import_kind| refinement) => pure "ref"
  | `(import_kind| implementation) => pure "imp"
  | `(import_kind| system) => pure "sys"
  | `(import_kind| pog) => pure "pog"
  | _ => Macro.throwUnsupported

/-- Import a B component into its own context; `qed` publishes its declarations. -/
syntax "import " import_kind ppSpace ident (" from " str)? : command

elab_rules : command
| `(command| import $kind:import_kind $name:ident $[from $path:str]?) => do
  let localName := name.getId.eraseMacroScopes
  let contextName := (← getCurrNamespace) ++ localName
  if (Barrel.obligationContexts.getState (← getEnv)).contexts.contains contextName then
    throwErrorAt name "Machine or POG `{contextName}` has already been imported."
  let ext ← liftMacroM <| extFromKind kind
  let path := System.FilePath.mk (path.map (·.getString) |>.getD ".")
  let fileName := localName.toString (escape := false)
  let filePath := path/System.FilePath.addExtension fileName ext
  let baseEnv ← getEnv
  let ((obligations, skipped), localEnv) ← withoutModifyingEnv' do
    let parsed ← match ext with
      | "pog" => pog2goals contextName.toString filePath
      | _ => mch2goals contextName.toString path filePath
    pog2obligations parsed contextName
  saveContext {
    name := contextName, path := ← IO.FS.realPath filePath, baseEnv, localEnv,
    obligations, skipped } (latest := true)

declare_syntax_cat obligation_proof
syntax "from " term : obligation_proof
syntax "by " Parser.Tactic.tacticSeq : obligation_proof

/-- Prove a single pending obligation, by its name or by its position in the import. -/
syntax (name := obligationCommand)
  ("next ")? "obligation" (ppSpace ident)? (" of " ident)?
  ppSpace obligation_proof : command

@[command_elab obligationCommand]
def elabObligation : CommandElab := fun stx => do
  let isNext := !stx[0].isNone
  let id? : Option (TSyntax `ident) := if stx[2].isNone then none else some ⟨stx[2][0]⟩
  let machine? : Option (TSyntax `ident) := if stx[3].isNone then none else some ⟨stx[3][1]⟩
  if isNext && id?.isSome then
    throwErrorAt stx "`next obligation` cannot specify an obligation name. Use `obligation <name>` instead."
  if !isNext && id?.isNone then
    throwErrorAt stx "Specify an obligation name, or use `next obligation`."
  let proof : Term ← if stx[4][0].getAtomVal == "from" then
      pure ⟨stx[4][1]⟩
    else
      let tac : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨stx[4][1]⟩
      `(term| by%$(stx[4][0]) $tac)
  let ctx ← resolveContext machine?
  proveObligation ctx id? proof stx

/-- Check completeness and publish the selected import's local declarations atomically. -/
syntax "qed" (ppSpace ident)? : command

elab_rules : command
| `(command| qed $[$name:ident]?) => do
  finalizeContext (← resolveContext name)
