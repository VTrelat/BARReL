import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew

open Lean Parser Elab Term Command

declare_syntax_cat discharger_command

syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command

syntax (name := pog_discharger) "pog_discharger " str withPosition((colEq discharger_command)*) : command

elab_rules : command
| `(command| pog_discharger $path $steps*) => do
  -- TODO: Plug POG reader and generate array of `Expr`

  let mut goals : Array Expr := #[
    .const ``True [],
    .const ``True []
  ]
  let mut i := 0

  let ns ← getCurrNamespace

  for step in steps do
    match step with
    | `(discharger_command| next $tac:tacticSeq) =>
      if goals.size = 0 then
        throwErrorAt step s!"No more goals to be discharged."

      let g := goals[i]!

      let decl : Declaration := .thmDecl {
        name := ns.str s!"thm{i}"
        levelParams := []
        type := g
        value := ← liftTermElabM do
          let e ← elabTerm (← `(term| by $tac)) (.some g) (catchExPostpone := false)
          synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          pure e
      }
      liftCoreM <| addDecl decl false

      i := i + 1

      pure .unit
    | _ => throwUnsupportedSyntax

  if i ≠ goals.size then
    let remaining := goals.size - i
    throwError s!"There still {if remaining = 1 then "is" else "are"} {remaining} goal{if remaining = 1 then "" else "s"} to discharge."

  pure .unit




namespace X
whatsnew in
pog_discharger "hello.pog"
next
  apply True.intro
next
  apply True.intro
