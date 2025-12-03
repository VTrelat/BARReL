import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import Barrel.Encoder
import POGReader.Basic
import Barrel.Meta

open Lean Parser Elab Term Command

declare_syntax_cat discharger_command
syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command
syntax (name := pogDischarger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command
syntax (name := mchDischarger) "mch_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

private structure ParserResult where
  name : String
  goals : Array (Name × String × Lean.Expr)

def pog2goals (pogPath : System.FilePath) (mch : Option (System.FilePath × UInt64) := .none)
  (steps : TSyntaxArray `discharger_command) :
    CommandElabM ParserResult := do
  let .some pogName := pogPath.fileStem | throwError "what?"

  let pog : String ← IO.FS.readFile pogPath
  let pogHash : UInt64 := hash pog

  if let .some pogHash' ← getPogHash pogPath then
    if pogHash = pogHash' then
      let .some goals ← getGoals pogHash | unreachable!
      return {
        name := pogName
        goals
      }

  let ns ← getCurrNamespace

  let goals ← do
    let mut wfs := #[]
    let mut res := #[]
    let mut i := 0

    let goals ← B.POG.extractGoals <$> B.POG.parse' pog
    for g in goals do
      let declName := ns |>.str pogName |>.str s!"{g.name}_{i}"
      -- NOTE: C'est caca
      let g' ← liftTermElabM <| g.toExpr wfs
      if g.name = "WellDefinednessAssertions" then
        wfs := wfs.push (declName, g')
      else
        res := res.push (declName, g.reason, g')

      trace[barrel.pog] "Generated theorem: {g'}"

      if let `(discharger_command| next%$tk $tac:tacticSeq) := steps[i]! then
        let e ← liftTermElabM do
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
        liftCoreM <| addDecl decl false
        liftTermElabM <| Lean.addDocStringOf false declName .missing
          (mkNode ``docComment #[
            mkAtom SourceInfo.none "/--",
            mkAtom SourceInfo.none s!"Machine `{pogName}`, proof obligation `{declName}`: {g.reason} -/"
          ])

      i := i + 1

    pure <| (wfs.map λ ⟨n, e⟩ ↦ ⟨n, "Assertion is well-defined", e⟩) ++ res

  -- if let .some (mchPath, mchHash) := mch then
  --   trace[barrel.pog] "Caching new machine file {mchPath}"
  --   registerFile mchPath pogPath mchHash pogHash goals
  -- else
  --   trace[barrel.pog] "Caching new POG file {pogPath}"
  --   registerFile "" pogPath 0 pogHash goals

  return {
    name := pogName
    goals
  }

def mch2goals (mchPath : System.FilePath) (steps : TSyntaxArray `discharger_command) : CommandElabM ParserResult := do
  let atelierBDir := System.FilePath.mk <| (← getOptions).getString `barrel.atelierb

  let .some mchName := mchPath.fileName | throwError "what?"
  let mchHash : UInt64 ← hash <$> IO.FS.readFile mchPath

  if let .some mchHash' ← getMchHash mchPath then
    if mchHash = mchHash' then
      -- Do not reparse the machine and POG
      let .some pogPath ← getPogPath mchPath | unreachable!
      let .some pogHash ← getPogHash pogPath | unreachable!
      let .some goals ← getGoals pogHash | unreachable!

      return {
        name := mchName
        goals
      }

  -- Parse the machine, generate the POG
  let stdout ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"bxml").toString, args := #["-a", mchPath.toString]
  }
  let tmp ← IO.FS.createTempDir
  let bxml := tmp/System.FilePath.withExtension mchName "bxml"
  IO.FS.writeFile bxml stdout
  let _ ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"pog").toString,
    args := #["-p", (atelierBDir/"include"/"pog"/"paramGOPSoftware.xsl").toString, "-w", bxml.toString]
  }

  -- Then parse the POG and generate the goals
  pog2goals (mch := (mchPath, mchHash)) (steps := steps) <| bxml.withExtension "pog"

def pog2obligations (res : ParserResult) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  -- TODO: check how we can also replay the proofs that we already have
  let ⟨name, goals⟩ := res

  let mut i := 0

  for step in steps do
    match step with
    | `(discharger_command| next%$tk $tac:tacticSeq) =>
      if i = goals.size then
        throwErrorAt step s!"No more goals to be discharged."

      let ⟨g_name, g_reason, g⟩ := goals[i]!

      if (← getOptions).getBool `barrel.show_goal_names true then
        logInfoAt tk m!"{g_name}: {g_reason}"

      -- let e ← liftTermElabM do
      --   let e ← elabTerm (← `(term| by%$tk $tac)) (.some g) (catchExPostpone := false)
      --   synthesizeSyntheticMVarsNoPostponing
      --   instantiateMVars e

      -- let levelParams := (collectLevelParams {} g).params ++ (collectLevelParams {} e).params

      -- let declName := g_name
      -- let decl : Declaration := .thmDecl {
      --   name := declName
      --   levelParams := levelParams.toList
      --   type := g
      --   value := e
      -- }
      -- liftCoreM <| addDecl decl false
      -- liftTermElabM <| Lean.addDocStringOf false declName .missing
      --   (mkNode ``docComment #[
      --     mkAtom SourceInfo.none "/--",
      --     mkAtom SourceInfo.none s!"Machine `{name}`, proof obligation `{g_name}`: {g_reason} -/"
      --   ])

      i := i + 1

      pure .unit
    | _ => throwUnsupportedSyntax

  if i ≠ goals.size then
    let remaining := goals.size - i
    throwError s!"There still {if remaining = 1 then "is" else "are"} {remaining} goal{if remaining = 1 then "" else "s"} to discharge."

elab_rules : command
| `(command| mch_discharger $path $steps*) => do
  pog2obligations (← mch2goals (System.FilePath.mk path.getString) steps) steps
| `(command| pog_discharger $path $steps*) => do
  pog2obligations (← pog2goals (System.FilePath.mk path.getString) (steps := steps)) steps
