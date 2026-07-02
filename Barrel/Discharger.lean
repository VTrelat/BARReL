import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import Barrel.Encoder
import POGReader.Basic
import Barrel.Meta
import Barrel.Tactics
import Barrel.Progress

open Lean Elab Term Command

declare_syntax_cat discharger_command
syntax withPosition("next " Parser.Tactic.tacticSeqIndentGt) : discharger_command

private structure ParserResult where
  path : System.FilePath
  name : String
  goals : Array B.POG.Goal

private def nameOf (mchPath : System.FilePath) : String :=
  mchPath.fileStem.get!

private def pog2goals (name : String) (pogPath : System.FilePath) (mchPath : Option System.FilePath := .none) : CommandElabM ParserResult := do
  let pog : String ← IO.FS.readFile pogPath
  let goals ← B.POG.extractGoals <$> B.POG.parse' pog

  return {
    path := match mchPath with | .some p => p | .none => pogPath
    name
    goals
  }

/--
  Canonical form for WD-condition lookup: binder names and `mdata` are erased. Bound
  variables are de Bruijn indices, so `==` on canonical forms is α-equivalence — enough to
  recognize the verbatim duplicates the encoder produces for repeated partial operators,
  without any `isDefEq` call.
-/
private partial def canonWD : Expr → Expr
  | .forallE _ t b bi => .forallE .anonymous (canonWD t) (canonWD b) bi
  | .lam _ t b bi     => .lam .anonymous (canonWD t) (canonWD b) bi
  | .letE _ t v b nd  => .letE .anonymous (canonWD t) (canonWD v) (canonWD b) nd
  | .app f a          => .app (canonWD f) (canonWD a)
  | .mdata _ e        => canonWD e
  | .proj n i e       => .proj n i (canonWD e)
  | e                 => e

/--
  All WD conditions seen so far in this import — auto-solved *and* leftover ones — keyed by
  the hash of their canonical form, so the lookup is a bucket scan instead of an `isDefEq`
  sweep over every previous condition.
-/
private abbrev SeenWDs := Std.HashMap UInt64 (Array (Name × Expr))

private def SeenWDs.insert' (seen : SeenWDs) (n : Name) (canon : Expr) : SeenWDs :=
  seen.insert canon.hash ((seen.getD canon.hash #[]).push (n, canon))

private def findWD (canon : Expr) (seen : SeenWDs) : TermElabM (Option Name) := do
  let .some bucket := seen[canon.hash]? | return .none
  for (n, e) in bucket do
    if e == canon then
      return n
    -- Hash collision, or a reducibility variant `==` cannot see: confirm with `isDefEq`.
    -- A runtime timeout here must count as "no match", not kill the enclosing import.
    if ← tryCatchRuntimeEx (Meta.isDefEq e canon) (fun _ ↦ pure false) then
      return n
  return .none

private def mch2goals (name : String) (dir mchPath : System.FilePath) : CommandElabM ParserResult := do
  let atelierBDir := System.FilePath.mk <| (← getOptions).getString `barrel.atelierb

  let mchName := nameOf mchPath

  -- Parse the machine, generate the POG
  let stdout ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"bxml").toString
    args := #["-I", dir.toString, "-a", mchPath.toString]
  }
  let cacheDir := (← getOptions).getString `barrel.cache_dir
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

private def pog2obligations (res : ParserResult) : CommandElabM PUnit := do
  let ⟨path, name, goals⟩ := res

  let ns ← getCurrNamespace

  let t0 ← IO.monoMsNow
  let nbPOs := goals.size
  let progress := (← getOptions).getBool `barrel.progress true

  -- let mut wds := #[]
  let mut res := #[]
  let mut wds : Array (Name × String × Expr) := #[]
  -- Every WD condition generated so far in this import, auto-solved or not: repeated
  -- partial operators produce the same condition over and over across obligations, and
  -- re-generating (and re-proving!) it for each theorem is what blew up the subgoal count.
  let mut seenWDs : SeenWDs := {}
  let mut autoDischarged := 0
  let mut nbGoals := goals.size
  let mut i := 0

  let mut skipped := 0
  let mut dedups := 0

  if progress then Barrel.Progress.report name 0 nbPOs 0 0 0 0 "" 0 0 false

  for g in goals do
    let declName := ns |>.str name |>.str s!"{g.name}_{i}"

    -- Encoding runs with its own heartbeat budget and its failures (unsupported construct,
    -- ill-typed translation, timeout) are confined to this obligation: on large industrial
    -- POGs a single unencodable goal must not abort the import of the thousands of others.
    let enc? : Option (Name × String × Expr × Array (Name × String × Expr × Bool) × SeenWDs × Nat) ←
      liftTermElabM <| withCurrHeartbeats <| tryCatchRuntimeEx
      (do
        let (g', wds'') ← g.toExpr

        let mut seen := seenWDs
        let mut wds' : Array (Name × String × Expr × Bool) := #[]
        let mut j := 0
        for ⟨g', mvar⟩ in wds'' do
          let n_wd := declName.str s!"wd_{j}"
          j := j + 1

          let g' ← instantiateMVars g'
          let canon := canonWD g'
          if let .some n ← findWD canon seen then
            trace[barrel.wd] "Found duplicated WD theorem: using {n} instead"
            mvar.assign (.const n [])
          else do
            mvar.assign (.const n_wd [])
            seen := seen.insert' n_wd canon
            wds' := wds'.push (n_wd, "Assertion is well-defined", g', true)

        -- A condition may mention WD metavariables that were only assigned later in the
        -- loop above (nested partial operators), so re-instantiate before anything is
        -- persisted across `liftTermElabM` boundaries, and register the *final* canonical
        -- forms — a metavariable from a dead `MetavarContext` must never leak.
        let wdsFinal ← wds'.mapM λ (n, r, e, b) ↦ do pure (n, r, ← instantiateMVars e, b)
        let seenFinal := wdsFinal.foldl (λ s (n, _, e, _) ↦ s.insert' n (canonWD e)) seenWDs

        let g' ← instantiateMVars g'
        trace[barrel] "Generated theorem: {g'}"

        pure <| .some (declName, g.reason, g', wdsFinal, seenFinal, wds''.size))
      fun ex => do
        logWarning m!"Failed to encode proof obligation `{declName}` ({g.reason}), skipping it:{indentD ex.toMessageData}"
        pure .none

    let .some (declName, reason, g', wds', seen, rawWDs) := enc?
      | skipped := skipped + 1
        nbGoals := nbGoals - 1
        i := i + 1
        continue
    seenWDs := seen
    dedups := dedups + (rawWDs - wds'.size)

    nbGoals := nbGoals + wds'.size
    let try_discharge := wds'.push (declName, reason, g', false)

    -- NOTE: Now try and solve it automatically...if possible
    for (declName, reason, g, isWd) in try_discharge do
      -- `withCurrHeartbeats` gives every subgoal its own full heartbeat budget, and
      -- `tryCatchRuntimeEx` is required because a heartbeat/recursion-depth timeout is a
      -- *runtime* exception, which an ordinary `try … catch` re-throws: without it a single
      -- diverging `barrel_solve` attempt aborts the whole `import` command instead of just
      -- leaving its obligation to the user.
      let (gOrWd, _hb) ← liftTermElabM <| withCurrHeartbeats do -- <| withOptions (Elab.async.set · false) do
        let hb₀ ← IO.getNumHeartbeats
        let r : _ ⊕ _ ← tryCatchRuntimeEx
          (do
            -- TODO: we should split on `isWd` to apply relevant tactics
            trace[barrel.solve] m!"Trying to solve theorem {declName} (isWd: {isWd}):{indentExpr g}"
            let e ← withoutErrToSorry do
              Meta.check g
              instantiateMVars =<< elabTermAndSynthesize (← `(term| by barrel_solve)) (.some g)

            trace[barrel.solve] m!"{Lean.checkEmoji} Success! (spent {((← IO.getNumHeartbeats) - hb₀) / 1000} heartbeats)"

            let levelParams := (collectLevelParams {} g).params ++ (collectLevelParams {} e).params

            let decl : Declaration := .thmDecl {
              name := declName
              levelParams := levelParams.toList
              type := g
              value := e
            }

            addDecl decl false

            Lean.addDocStringOf false declName .missing
              (mkNode ``Parser.Command.docComment #[
                mkAtom "/--",
                mkAtom s!"Machine `{name}`, proof obligation `{declName}`: {reason} -/"
              ])

            pure <| .inl PUnit.unit)
          fun ex => do
            trace[barrel.solve] m!"{Lean.crossEmoji} Failed! (spent {((← IO.getNumHeartbeats) - hb₀) / 1000} heartbeats)\n{ex.toMessageData}"

            pure <| .inr (declName, reason, g, isWd)
        pure (r, ((← IO.getNumHeartbeats) - hb₀) / 1000)

      match gOrWd with
      | .inl _ => autoDischarged := autoDischarged + 1
      | .inr (declName, reason, g, isWd) =>
        let goal := (declName, reason, g)
        if isWd then wds := wds.push goal else res := res.push goal

      if progress then
        let elapsed := (← IO.monoMsNow) - t0
        let eta := elapsed * (nbPOs - (i + 1)) / (i + 1)
        Barrel.Progress.report name (i + 1) nbPOs nbGoals autoDischarged (wds.size + res.size) skipped
          declName.toString elapsed eta false

    i := i + 1

  let goals := wds ++ res
  let dt := (← IO.monoMsNow) - t0

  let wdDistinct := nbGoals - (nbPOs - skipped)
  let pct := if nbGoals == 0 then 0 else autoDischarged * 1000 / nbGoals
  let rows : Array (String × String) := #[
    ("auto-solved", s!"{autoDischarged} / {nbGoals} ({pct / 10}.{pct % 10}%)"),
    ("WD goals", s!"{wdDistinct} unique (+{dedups} reused)"),
    ("remaining", s!"{goals.size}")
  ]
  if progress then
    Barrel.Progress.report name nbPOs nbPOs nbGoals autoDischarged goals.size skipped "" dt 0 true
      (summary := Json.arr <| rows.map λ (l, v) ↦ Json.arr #[.str l, .str v])

  if skipped > 0 then
    logWarning s!"Skipped {skipped} proof obligation{if skipped = 1 then "" else "s"} that could not be encoded."
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

  let absPath ← IO.FS.realPath path
  modifyEnv (nameFromPath.modifyState · λ map ↦ map.insert name absPath)
  modifyEnv (cache.modifyState · λ map ↦ map.insert absPath goals)

private def obligations2theorems (name : String) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  let env ← getEnv
  let .some path := nameFromPath.getState env |>.find? name
    | throwError "Machine or POG named {name} not found.\nMake sure to import it with `import`."
  let .some goals := cache.getState env |>.find? path
    | throwError "Impossible!"
  let mut proofs_missing := 0
  let mut i := 0

  -- TODO: check how we can also replay the proofs that we already have
  for ⟨declName, r_reason, g'⟩ in goals do
    if let .some (step : TSyntax `discharger_command) := steps[i]? then
      if let `(discharger_command| next%$tk $tac:tacticSeq) := step then
        if (← getOptions).getBool `barrel.show_goal_names true then
          logInfoAt tk m!"{declName}: {r_reason}"

        -- Fresh heartbeat budget per obligation, so one expensive user proof does not eat
        -- into the budget of the ones replayed after it.
        liftTermElabM <| withCurrHeartbeats do -- <| withOptions (Elab.async.set · false) do
          let g' ← instantiateMVars g'
          if g'.hasExprMVar then
            throwError "Resulting expression contains metavariables{indentExpr g'}"

          let e ← do
            let e ← elabTerm (← `(term| by%$tk $tac)) (.some g') (catchExPostpone := false)
            synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e

          let levelParams := (collectLevelParams {} g').params ++ (collectLevelParams {} e).params

          let decl : Declaration := .thmDecl {
            name := declName
            levelParams := levelParams.toList
            type := g'
            value := e
          }

          addDecl decl false

          Lean.addDocStringOf false declName .missing
            (mkNode ``Parser.Command.docComment #[
              mkAtom "/--",
              mkAtom s!"Machine `{name}`, proof obligation `{declName}`: {r_reason} -/"
            ])
    else
      proofs_missing := proofs_missing + 1

    i := i + 1

  if proofs_missing > 0 then
    throwError s!"There still {if proofs_missing = 1 then "is" else "are"} {proofs_missing} goal{if proofs_missing = 1 then "" else "s"} to discharge."
  else if steps.size > goals.size then
    let `(discharger_command| next%$tk $_) := steps[i]! | unreachable!
    throwErrorAt tk "There are no more goals to discharge."

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

/--
  Process a B machine/system/pog and add the theorems to be discharged into the environment.

  Live progress is shown by the global panel widget registered in `Barrel.Progress` (active
  from the file's first line, so it is already on screen when this — possibly long — command
  starts): each obligation here reports into a shared `IO.Ref`, and the widget polls it. Park
  the cursor on any already-elaborated line to watch the cards fill in live.
-/
@[incremental]
elab "import " kind:import_kind ppSpace name:ident " from " path:str : command => do
  let name := name.getId.getString!
  let ext ← liftMacroM <| extFromKind kind
  let path := System.FilePath.mk path.getString
  let filePath := path/System.FilePath.addExtension name ext
  -- TODO: verify a snapshot etc, so that the files are only re-generated/re-parsed when changed or the first time
  pog2obligations =<< match ext with
    | "pog" => pog2goals name filePath
    | _ => mch2goals name path filePath

/--
  Provide the proofs for the theorems generated from a given machine.
-/
elab "prove_obligations_of " name:ident ppLine steps:withPosition((colEq discharger_command)*) : command => do
  obligations2theorems name.getId.getString! steps
