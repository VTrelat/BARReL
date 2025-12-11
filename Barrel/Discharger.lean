import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import Barrel.Encoder
import POGReader.Basic
import Barrel.Meta
import Barrel.Tactics

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

private def findWF (g : Expr) (wfs : Array (Name × String × Expr)) (wfs' : Array (Name × String × Expr × Bool)) : TermElabM (Option Name) := do
  if let .some (n, _, _) ← wfs.findM? λ (_, _, g') ↦ Meta.isDefEq g g' then
    return n
  else if let .some (n, _, _, _) ← wfs'.findM? λ (_, _, g', _) ↦ Meta.isDefEq g g' then
    return n
  else
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
      Although `pog` can generate the WF conditions for us (with the `-w` flag), we will not be using these.

      Reasons are:
      * The WF conditions are placed at the very end of the `.pog` file, while we would need to
        reference this in our main goals.
      * Knowing whether a goal is a WF condition requires parsing its description, which is very
        fragile and error-prone.
      * Even with these issues ironed out, we would still need complicated logic in order to correctly
        instantiate those conditions in our goals (which is even worse in the cases where a WF condition
        may depend on the previous conjunct, e.g. in goals like `∃ G. G ∈ A ⟶ B ∧ G(x) ∈ B`, where the
        generated WF condition is `∀ G. G ∈ A ⟶ B ⇒ x ∈ dom(G) ∧ G ∈ dom(G) ⇸ ran(G)`).
    -/
    args := #["-p", (atelierBDir/"include"/"pog"/"paramGOPSoftware.xsl").toString, /- "-w", -/ bxml.toString]
  }

  -- Then parse the POG and generate the goals
  pog2goals name (mchPath := mchPath) <| bxml.withExtension "pog"

private def pog2obligations (res : ParserResult) : CommandElabM PUnit := do
  let ⟨path, name, goals⟩ := res

  let ns ← getCurrNamespace

  -- let mut wfs := #[]
  let mut res := #[]
  let mut wfs : Array (Name × String × Expr) := #[]
  let mut autoDischarged := 0
  let mut nbGoals := goals.size
  let mut i := 0

  for g in goals do
    let declName := ns |>.str name |>.str s!"{g.name}_{i}"

    let (declName, reason, g', wfs') ← liftTermElabM do
      let (g', wfs'') ← g.toExpr

      let mut wfs' : Array (Name × String × Expr × Bool) := #[]
      let mut j := 0
      for ⟨g', mvar⟩ in wfs'' do
        let n_wf := declName.str s!"wf_{j}"
        j := j + 1

        if let .some n ← findWF g' wfs wfs' then -- ← (wfs ++ wfs'.map λ (a, b, c, d) ↦ ((a : Name), (b : String), (c : Expr))).findM? λ (_, _, g'') ↦ Meta.isDefEq g' g'' then
          trace[barrel.wf] "Found duplicated WF theorem: using {n} instead"
          mvar.assign (.const n [])
        else do
          mvar.assign (.const n_wf [])
          let g' ← instantiateMVars g'
          wfs' := wfs'.push (n_wf, "Assertion is well-defined", g', true)

      let g' ← instantiateMVars g'
      trace[barrel] "Generated theorem: {g'}"

      pure (declName, g.reason, g', wfs')

    nbGoals := nbGoals + wfs'.size
    let try_discharge := wfs'.push (declName, reason, g', false)

    -- NOTE: Now try and solve it automatically...if possible
    for (declName, reason, g, isWf) in try_discharge do
      let gOrWf : _ ⊕ _ ← liftTermElabM do -- <| withOptions (Elab.async.set · false) do
        try
          trace[barrel.solve] m!"Trying to solve theorem {declName} (isWf: {isWf}):{indentExpr g}"
          let e ← withoutErrToSorry do
            Meta.check g
            instantiateMVars =<< elabTermAndSynthesize (← `(term| by barrel_solve)) (.some g)

          trace[barrel.solve] m!"{Lean.checkEmoji} Success!"

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

          pure <| .inl PUnit.unit
        catch ex =>
          trace[barrel.solve] m!"{Lean.crossEmoji} Failed!\n{ex.toMessageData}"

          pure <| .inr (declName, reason, g, isWf)

      match gOrWf with
      | .inl _ => autoDischarged := autoDischarged + 1
      | .inr (declName, reason, g, isWf) =>
        let goal := (declName, reason, g)
        if isWf then wfs := wfs.push goal else res := res.push goal

    i := i + 1

  let goals := wfs ++ res
  if (← getOptions).getBool `barrel.show_auto_solved && autoDischarged > 0 then
    logInfo s!"🎉 Automatically solved {autoDischarged} out of {nbGoals} subgoals!"

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

        liftTermElabM do -- <| withOptions (Elab.async.set · false) do
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

private def extFromKind : TSyntax `import_kind → MacroM String
  | `(import_kind| machine) => pure "mch"
  | `(import_kind| refinement) => pure "ref"
  | `(import_kind| system) => pure "sys"
  | `(import_kind| pog) => pure "pog"
  | _ => Macro.throwUnsupported

/--
  Process a B machine/system/pog and add the theorems to be discharged into the environment.
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
