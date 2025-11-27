import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import B4Lean.Encoder

import POGReader_.Basic
import B4Lean.Elab

open Lean Parser Elab Term Command

declare_syntax_cat discharger_command

syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command

syntax (name := pog_discharger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

elab_rules : command
| `(command| pog_discharger $path $steps*) => do
  -- let pogPath ← mch2pog (System.FilePath.mk path.getString)
  let path := System.FilePath.mk path.getString
  let goals ← B.POG.parseAndExtractGoals path
  -- let pog ← readPOG path |>.propagateError
  -- let ⟨_, pogState⟩ ← POGtoB pog |>.run ∅ |>.propagateError

  -- let goals ← liftTermElabM pogState.env.mkGoal
  -- let goals := goals.toArray

  let mut i := 0

  let ns ← getCurrNamespace
  let .some name := path.fileStem | throwError "what?"

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

-- set_option trace.b4lean.pog true

open scoped B.Builtins

pog_discharger "specs/Counter.pog"
next
  grind
next
  grind
next
  rintro x ⟨_, _⟩ _ _
  grind
next
  grind

pog_discharger "specs/Nat.pog"
next
  rintro x ⟨_, _⟩
  assumption

pog_discharger "specs/Collect.pog"
next
  grind

pog_discharger "specs/Forall.pog"
next
  grind

pog_discharger "specs/Exists.pog"
next
  exists 0, 0

-- pog_discharger "specs/Injective.pog"
-- next
  -- admit

-- #check Counter.Initialisation_0
-- #check Counter.Initialisation_1
-- #check Counter.Operation_inc_2
-- #check Counter.Operation_inc_3
-- #check Nat.Initialisation_0
