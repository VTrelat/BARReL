import Lean.Elab.Command
import Lean.Elab.BuiltinTerm
import Mathlib.Util.WhatsNew
import Barrel.Encoder
import POGReader.Basic
import Barrel.Meta

open Lean Parser Elab Term Command

private structure ParserResult where
  name : String
  goals : Array (String × String × Lean.Expr)

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

  let goals ← do
    let goals ← B.POG.extractGoals <$> B.POG.parse' pog
    liftTermElabM <| goals.mapM λ g ↦ (Prod.mk g.name ∘ Prod.mk g.reason) <$> g.toExpr

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
  pog2goals (mch := (mchPath, mchHash)) <| bxml.withExtension "pog"

declare_syntax_cat discharger_command
syntax withPosition("next " Tactic.tacticSeqIndentGt) : discharger_command
syntax (name := pogDischarger) "pog_discharger " str ppSpace withPosition((colEq discharger_command)*) : command
syntax (name := mchDischarger) "mch_discharger " str ppSpace withPosition((colEq discharger_command)*) : command

def pog2obligations (res : ParserResult) (steps : TSyntaxArray `discharger_command) : CommandElabM PUnit := do
  -- TODO: check how we can also replay the proofs that we already have
  let ⟨name, goals⟩ := res
  let ns ← getCurrNamespace

  let mut i := 0

  for step in steps do
    match step with
    | `(discharger_command| next%$tk $tac:tacticSeq) =>
      if i = goals.size then
        throwErrorAt step s!"No more goals to be discharged."

      let ⟨g_name, g_reason, g⟩ := goals[i]!

      if (← getOptions).getBool `barrel.show_goal_names true then
        logInfoAt tk m!"{g_name}: {g_reason}"

      let e ← liftTermElabM do
        let e ← elabTerm (← `(term| by%$tk $tac)) (.some g) (catchExPostpone := false)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e

      let levelParams := (collectLevelParams {} g).params ++ (collectLevelParams {} e).params

      let declName := ns |>.str name |>.str s!"{g_name}_{i}"
      let decl : Declaration := .thmDecl {
        name := declName
        levelParams := levelParams.toList
        type := g
        value := e
      }
      liftCoreM <| addDecl decl false
      liftTermElabM <| Lean.addDocStringOf false declName .missing
        (mkNode ``docComment #[
          mkAtom SourceInfo.none "/--",
          mkAtom SourceInfo.none s!"Machine `{name}`, proof obligation `{g_name}`: {g_reason} -/"
        ])

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
