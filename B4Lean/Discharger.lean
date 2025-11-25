import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import B4Lean.Encoder

import POGReader.POGReader
import B4Lean.Elab

open Lean Parser Elab Term Command

declare_syntax_cat discharger_command

syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command

syntax (name := pog_discharger) "pog_discharger " str withPosition((colEq discharger_command)*) : command

elab_rules : command
| `(command| pog_discharger $path $steps*) => do
  -- let pogPath ← mch2pog (System.FilePath.mk path.getString)
  let pog ← readPOG (System.FilePath.mk path.getString) |>.propagateError
  let ⟨_, pogState⟩ ← POGtoB pog |>.run ∅ |>.propagateError

  let goals ← liftTermElabM <| Meta.liftMetaM pogState.env.mkGoal
  let goals := goals.toArray

  let mut i := 0

  let ns ← getCurrNamespace

  for step in steps do
    match step with
    | `(discharger_command| next $tac:tacticSeq) =>
      if i = goals.size then
        throwErrorAt step s!"No more goals to be discharged."

      let ⟨n, g⟩ := goals[i]!

      let decl : Declaration := .thmDecl {
        name := ns.str s!"{n}_{i}"
        levelParams := []
        type := g
        value := ← liftTermElabM do
          let e ← elabTerm (← `(term| by $tac)) (.some g) (catchExPostpone := false)
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
      }
      liftCoreM <| addDecl decl false

      i := i + 1

      pure .unit
    | _ => throwUnsupportedSyntax

  if i ≠ goals.size then
    let remaining := goals.size - i
    throwError s!"There still {if remaining = 1 then "is" else "are"} {remaining} goal{if remaining = 1 then "" else "s"} to discharge."

  pure .unit

pog_discharger "specs/Nat.pog"
next
  intro x
  admit
