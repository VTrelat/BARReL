import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import Barrel.Encoder
import POGReader.Basic
import Barrel.Meta

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

private def mch2goals (name : String) (mchPath : System.FilePath) : CommandElabM ParserResult := do
  let atelierBDir := System.FilePath.mk <| (← getOptions).getString `barrel.atelierb

  let mchName := nameOf mchPath

  -- Parse the machine, generate the POG
  let stdout ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"bxml").toString, args := #["-a", mchPath.toString]
  }
  let tmp ← IO.FS.createTempDir
  let bxml := tmp/System.FilePath.addExtension mchName "bxml"
  IO.FS.writeFile bxml stdout
  let _ ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"pog").toString,
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
  let mut i := 0

  for g in goals do
    let declName := ns |>.str name |>.str s!"{g.name}_{i}"

    let (declName, reason, g', wfs') ← liftTermElabM do
      let (g', wfs'') ← g.toExpr

      let mut wfs' : Array (Name × String × Expr) := #[]
      let mut j := 0
      for ⟨g', mvar⟩ in wfs'' do
        let n_wf := declName.str s!"wf_{j}"
        j := j + 1

        if let .some (n, _, _) ← (wfs ++ wfs').findM? λ (_, _, g'') ↦ Meta.isDefEq g' g'' then
          trace[barrel.wf] "Found duplicated WF theorem: using {n} instead"
          mvar.assign (.const n [])
        else do
          mvar.assign (.const n_wf [])
          let g' ← instantiateMVars g'
          wfs' := wfs'.push (n_wf, "Assertion is well-defined", g')

      let g' ← instantiateMVars g'
      trace[barrel] "Generated theorem: {g'}"

      pure (declName, g.reason, g', wfs')

    res := res.push (declName, reason, g')
    wfs := wfs ++ wfs'
    i := i + 1

  modifyEnv (nameFromPath.modifyState · λ map ↦ map.insert name path)
  modifyEnv (cache.modifyState · λ map ↦ map.insert path (wfs ++ res))

private def obligations2theorems (name : String) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  let env ← getEnv
  let .some path := nameFromPath.getState env |>.find? name
    | throwError "Machine or POG named {name} not found.\nMake sure to import it with `import_mch` or `import_pog`."
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

        liftTermElabM <| withOptions (Elab.async.set · false) do
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

private def extFromKind : TSyntax `import_kind → MacroM String
  | `(import_kind| machine) => pure "mch"
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
  let path := System.FilePath.mk path.getString/System.FilePath.addExtension name ext
  -- TODO: verify a snapshot etc, so that the files are only re-generated/re-parsed when changed or the first time
  pog2obligations =<< match ext with
    | "pog" => pog2goals name path
    | _ => mch2goals name path

/--
  Provide the proofs for the theorems generated from a given machine.
-/
elab "prove_obligations_of " name:ident ppLine steps:withPosition((colEq discharger_command)*) : command => do
  obligations2theorems name.getId.getString! steps
