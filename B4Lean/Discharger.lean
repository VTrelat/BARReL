import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import B4Lean.Encoder
import POGReader.Basic
import B4Lean.Meta
-- import B4Lean.Elab

open Lean Parser Elab Term Command

private structure ParserResult where
  name : String
  goals : Array B.POG.Goal

def pog2goals (pogPath : System.FilePath) (mch : Option (System.FilePath × UInt64) := .none) : CommandElabM ParserResult := do
  let .some pogName := pogPath.fileName | throwError "what?"

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
    args := #["-p", (atelierBDir/"include"/"pog"/"paramGOPSoftware.xsl").toString, bxml.toString]
  }

  -- Then parse the POG and generate the goals
  pog2goals (mch := (mchPath, mchHash)) <| bxml.withExtension "pog"

declare_syntax_cat discharger_command
syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command
syntax (name := pogDischarger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command
syntax (name := mchDischarger) "mch_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

inductive Path
  | mch : System.FilePath → Path
  | pog : System.FilePath → Path

def pog2obligations (res : ParserResult) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  -- TODO: check how we can also replay the proofs that we already have
  let name := res.name
  let goals := res.goals

  let mut i := 0

  let ns ← getCurrNamespace

  for step in steps do
    match step with
    | `(discharger_command| next $tac:tacticSeq) =>
      if i = goals.size then
        throwErrorAt step s!"No more goals to be discharged."

      let g := goals[i]!
      let g_name := g.name

      let g ← liftTermElabM g.toExpr
      let e ← liftTermElabM do
        let e ← elabTerm (← `(term| by $tac)) (.some g) (catchExPostpone := false)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e

      let levelParams := (collectLevelParams {} g).params ++ (collectLevelParams {} e).params

      let decl : Declaration := .thmDecl {
        name := ns |>.str name |>.str s!"{g_name}_{i}"
        levelParams := levelParams.toList
        type := g
        value := e
      }
      liftCoreM <| addDecl decl false

      i := i + 1

      pure .unit
    | _ => throwUnsupportedSyntax

  if i ≠ goals.size then
    let remaining := goals.size - i
    throwError s!"There still {if remaining = 1 then "is" else "are"} {remaining} goal{if remaining = 1 then "" else "s"} to discharge."

elab_rules : command
| `(command| mch_discharger $path $steps*) => do
  pog2obligations (← mch2goals <| System.FilePath.mk path.getString) steps
| `(command| pog_discharger $path $steps*) => do
  pog2obligations (← pog2goals <| System.FilePath.mk path.getString) steps
