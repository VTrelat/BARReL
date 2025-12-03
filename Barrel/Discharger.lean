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
  goals : Array B.POG.Goal

def pog2goals (pogPath : System.FilePath) (mch : Option (System.FilePath × UInt64) := .none) : CommandElabM ParserResult := do
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

  let goals ← B.POG.extractGoals <$> B.POG.parse' pog

  if let .some (mchPath, mchHash) := mch then
    trace[barrel.pog] "Caching new machine file {mchPath}"
    registerFile mchPath pogPath mchHash pogHash goals
  else
    trace[barrel.pog] "Caching new POG file {pogPath}"
    registerFile "" pogPath 0 pogHash goals

  return {
    name := pogName
    goals
  }

def mch2goals (mchPath : System.FilePath) : CommandElabM ParserResult := do
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
  pog2goals (mch := (mchPath, mchHash)) <| bxml.withExtension "pog"

def pog2obligations (res : ParserResult) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  -- TODO: check how we can also replay the proofs that we already have
  let ⟨name, goals⟩ := res

  let ns ← getCurrNamespace

  let mut wfs := #[]
  let mut res := #[]
  let mut i := 0
  let mut proofs_missing := 0

  for g in goals do
    let declName := ns |>.str name |>.str s!"{g.name}_{i}"

    let g' ← liftTermElabM <| g.toExpr wfs
    if g.name = "WellDefinednessAssertions" then
      wfs := wfs.push (declName, g')
    else
      res := res.push (declName, g.reason, g')

    trace[barrel.pog] "Generated theorem: {g'}"

    if let .some (step : TSyntax `discharger_command) := steps[i]? then
      if let `(discharger_command| next%$tk $tac:tacticSeq) := step then
        if (← getOptions).getBool `barrel.show_goal_names true then
          logInfoAt tk m!"{g.name}: {g.reason}"

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
            mkAtom SourceInfo.none s!"Machine `{name}`, proof obligation `{declName}`: {g.reason} -/"
          ])
    else
      proofs_missing := proofs_missing + 1

    i := i + 1

  if proofs_missing > 0 then
    throwError s!"There still {if proofs_missing = 1 then "is" else "are"} {proofs_missing} goal{if proofs_missing = 1 then "" else "s"} to discharge."

elab_rules : command
| `(command| mch_discharger $path $steps*) => do
  pog2obligations (← mch2goals (System.FilePath.mk path.getString)) steps
| `(command| pog_discharger $path $steps*) => do
  pog2obligations (← pog2goals (System.FilePath.mk path.getString)) steps
