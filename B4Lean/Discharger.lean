import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import B4Lean.Encoder
import POGReader.Basic
-- import B4Lean.Elab

open Lean Parser Elab Term Command

declare_syntax_cat discharger_command
syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command
syntax (name := pog_discharger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

def mch2pog (mchPath : System.FilePath) : CommandElabM System.FilePath := do
  let atelierBDir : System.FilePath :=
    System.FilePath.mk <| (← getOptions).getString `b4lean.atelierb

  let stdout ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"bxml").toString, args := #["-a", mchPath.toString]
  }
  let tmp ← IO.FS.createTempDir
  let bxml := tmp/"tmp.bxml"
  IO.FS.writeFile bxml stdout
  let _ ← IO.Process.run {
    cmd := (atelierBDir/"bin"/"pog").toString,
    args := #["-p", (atelierBDir/"include"/"pog"/"paramGOPSoftware.xsl").toString, bxml.toString]
  }
  pure <| bxml.withExtension "pog"

elab_rules : command
| `(command| pog_discharger $path $steps*) => do
  let path := System.FilePath.mk path.getString
  let .some name := path.fileStem | throwError "what?"
  let path ← mch2pog path
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
        let e ← elabTerm (← `(term| by skip; · $tac)) (.some g) (catchExPostpone := false)
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

  pure .unit

/- TESTS -/

-- set_option trace.b4lean.pog true
set_option b4lean.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

pog_discharger "specs/Counter.mch"
next
  grind
next
  grind
next
  rintro x ⟨_, _⟩ _ _
  grind
next
  grind

pog_discharger "specs/Nat.mch"
next
  rintro x ⟨_, _⟩
  assumption

pog_discharger "specs/Collect.mch"
next
  grind

pog_discharger "specs/Forall.mch"
next
  grind

pog_discharger "specs/Exists.mch"
next
  exists 0, 0

pog_discharger "specs/Injective.mch"
next
  admit

pog_discharger "specs/HO.mch"
next
  admit

pog_discharger "specs/Enum.mch"
next
  grind

-- #check Counter.Initialisation_0
-- #check Counter.Initialisation_1
-- #check Counter.Operation_inc_2
-- #check Counter.Operation_inc_3
-- #check Nat.Initialisation_0
