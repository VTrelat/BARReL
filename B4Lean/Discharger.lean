import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import B4Lean.Encoder
import POGReader.Basic
-- import B4Lean.Elab

open Lean Parser Elab Term Command

def mch2pog (mchPath : System.FilePath) : CommandElabM System.FilePath := do
  let atelierBDir := System.FilePath.mk <| (← getOptions).getString `b4lean.atelierb

  let .some mchName := mchPath.fileName | throwError "what?"

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
  pure <| bxml.withExtension "pog"

declare_syntax_cat discharger_command
syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command
syntax (name := pogDischarger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command
syntax (name := mchDischarger) "mch_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

def pog2obligations (path : System.FilePath) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  let .some name := path.fileStem | throwError "what?"
  let goals ← B.POG.parseAndExtractGoals path

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
  pog2obligations (← mch2pog <| System.FilePath.mk path.getString) steps
| `(command| pog_discharger $path $steps*) => do
  pog2obligations (System.FilePath.mk path.getString) steps
