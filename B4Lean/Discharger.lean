import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import B4Lean.Encoder

import POGReader.POGReader
import B4Lean.Elab

open Lean Parser Elab Term Command

declare_syntax_cat discharger_command

syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command

syntax (name := pog_discharger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

elab_rules : command
| `(command| pog_discharger $path $steps*) => do
  -- let pogPath ← mch2pog (System.FilePath.mk path.getString)
  let pog ← readPOG (System.FilePath.mk path.getString) |>.propagateError
  let ⟨_, pogState⟩ ← POGtoB pog |>.run ∅ |>.propagateError

  let goals ← liftTermElabM pogState.env.mkGoal
  let goals := goals.toArray

  let mut i := 0

  let ns ← getCurrNamespace

  for step in steps do
    match step with
    | `(discharger_command| next $tac:tacticSeq) =>
      if i = goals.size then
        throwErrorAt step s!"No more goals to be discharged."

      let ⟨n, g⟩ := goals[i]!
      let e ← liftTermElabM do
        let e ← elabTerm (← `(term| by $tac)) (.some g) (catchExPostpone := false)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e

      let levelParams := (collectLevelParams {} g).params ++ (collectLevelParams {} e).params

      let decl : Declaration := .thmDecl {
        name := ns.str s!"{n}_{i}"
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

set_option trace.b4lean.pog true

pog_discharger "specs/Nat.pog"
next
  rintro x ⟨_, rfl, _, _, _⟩
  assumption

set_option pp.rawOnError true in
-- set_option pp.all true in
#print Initialisation_0
