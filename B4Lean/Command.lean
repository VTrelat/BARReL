import B4Lean.Elab
import B.Environment
import Extra.Utils
import Lean.Data.Xml
import Std.Data.HashSet
import Lean.Data.RBMap

open Lean System

namespace B

/-- Heuristic type inference for a subset of B terms. -/
def inferBType : Term → Option BType
  | .ℤ => return .set .int
  | .𝔹 => return .set .bool
  | .pow A => .set <$> inferBType A
  | .cprod A B => return .set (.prod (← inferBType A) (← inferBType B))
  | .collect _ D _ => inferBType D
  | .pfun A B => return .set (.prod (← inferBType A) (← inferBType B))
  | .union S _ => inferBType S
  | .inter S _ => inferBType S
  | .card _ => return .int
  | .app f _ => do
    let .set (.prod _ σ) ← inferBType f | none
    return σ
  | .lambda _ D f => do
    let τ ← inferBType D
    let σ ← inferBType f
    return .set (.prod τ σ)
  | .maplet x y => do
    let τ ← inferBType x
    let σ ← inferBType y
    return .prod τ σ
  | .min S => inferBType S
  | .max S => inferBType S
  | .all .. => return .bool
  | .var _ => none
  | .int _ => return .int
  | .bool _ => return .bool
  | .add _ _ | .sub _ _ | .mul _ _ => return .int
  | .and _ _ | .not _ | .eq _ _ | .mem _ _ | .le _ _ => return .bool

/--
Translate B terms to Lean code (as a string) so the generated POs elaborate.
This is intentionally shallow; extend as needed.
-/
partial def Term.toLean : Term -> Nat -> Std.Format
  | .var v => λ _ => v
  | .int n => λ _ => toString n
  | .bool x => λ _ => toString x
  | .ℤ => λ _ => "Set.univ"
  | .𝔹 => λ _ => "Set.univ"
  | .imp x y => «infixr» Term.toLean 30 "→" x y -- /!\ see manrefb p.198
  | .or x y => «infixl» Term.toLean 40 "∨" x y
  | .and x y => «infixl» Term.toLean 40 "∧" x y
  | .eq x y => «infix» Term.toLean 40 "=" x y
  | .mem x S => «infixl» Term.toLean 120 "∈" x S
  | .brel x y => «infix» Term.toLean 125 "↔" x y
  | .pfun A B => «infixr» Term.toLean 125 "⇸" A B
  | .neq x y => «infix» Term.toLean 160 "≠" x y
  | .le x y => «infixl» Term.toLean 160 "≤" x y
  | .inter x y => «infixl» Term.toLean 160 "∩" x y
  | .union x y => «infixl» Term.toLean 160 "∪" x y
  | .maplet x y => «infixl» Term.toLean 160 "↦" x y
  | .add x y => «infixl» Term.toLean 180 "+" x y
  | .sub x y => «infixl» Term.toLean 180 "-" x y
  | .mul x y => «infixl» Term.toLean 190 "*" x y
  | .cprod x y => «infixl» Term.toLean 190 "⨯" x y
  | .exists v D P =>
    let τ := match inferBType D with
      | some (.set σ) => σ
      | _ => panic! s!"inferBType:exists: cannot infer type of {D}"
    let vs := v.map Term.var
    let v_folded := vs.reverse.tail.foldl (fun acc vᵢ => .maplet vᵢ acc) vs.getLast!
    let v_mem_D_and_P := (v_folded ∈ᴮ D) ∧ᴮ P
    binder'' Term.toLean BType.pretty 250 "∃ " v.toString' " : " τ ", " v_mem_D_and_P ""
  | .all v D P =>
    let τ := match inferBType D with
      | some (.set σ) => σ
      | _ => panic! s!"inferBType:all: cannot infer type of {D}"
    let vs := v.map Term.var
    let v_folded := vs.reverse.tail.foldl (fun acc vᵢ => .maplet vᵢ acc) vs.getLast!
    let v_mem_D_imp_P := (v_folded ∈ᴮ D) ⇒ᴮ P
    binder'' Term.toLean BType.pretty 0 "∀ " v.toString' " : " τ ", " v_mem_D_imp_P ""
  | .collect v D P =>
    let τ := match inferBType D with
      | some (.set σ) => σ
      | _ => panic! "inferBType:collect: cannot infer type of {D}"
    let vs := v.map Term.var
    let v_folded := vs.reverse.tail.foldl (fun acc vᵢ => .maplet vᵢ acc) vs.getLast!
    let v_mem_D_imp_P := (v_folded ∈ᴮ D) ⇒ᴮ P
    binder'' Term.toLean BType.pretty 250 "{ " v.toString' " : " τ " | " v_mem_D_imp_P " }"
  | .lambda v D P =>
    let τ := match inferBType D with
      | some t => t
      | none => panic! s!"inferBType:lambda: cannot infer type of {D}"
    binder Term.toLean 0 "λ " v.toString' " : " τ.toTerm " ↦ " P ""
  | .not x => «prefix» Term.toLean 250 "¬ " x
  | .app f x => λ _ => Term.toLean f 300 ++ .paren (Term.toLean x 0)
  | .pow S => «prefix» (Term.toLean) 290 "𝒫 " S
  | .min S => «prefix» (Term.toLean) 290 "min " S
  | .max S => «prefix» (Term.toLean) 290 "max " S
  | .card S => λ _ => "‖" ++ Term.toLean S 0 ++ "‖"
/-- Translate a B boolean term into Lean `Prop` (as code). -/
def Term.toLeanProp (t : Term) : String :=
  t.toLean 0 |> toString

def BType.toLean : BType → String
  | .int => "Int"
  | .bool => "Bool"
  | .set τ => s!"Set ({τ.toLean})"
  | .prod α β => s!"({α.toLean} × {β.toLean})"

end B

namespace B4Lean

structure PONameInfo where
  tag : String
  goalTags : Array (Option String)
deriving Inhabited

structure GoalSummary where
  theoremName : String
  poTag : String
  simpleTag? : Option String
  defs : List B.Term
  hyps : List B.Term
  goal : B.Term
  goalIndex : Nat
  totalGoals : Nat
deriving Inhabited

private def collectCharacters (content : Array Xml.Content) : String :=
  content.foldl (init := "") fun acc c =>
    match c with
    | Xml.Content.Character s => acc ++ s
    | _ => acc

private def extractTagText (content : Array Xml.Content) : Option String :=
  content.findSome? fun
    | Xml.Content.Element ⟨"Tag", _, inner⟩ =>
      let txt := (collectCharacters inner).trim
      if txt.isEmpty then none else some txt
    | _ => none

private def parsePOInfos : Xml.Element → Except String (Array PONameInfo)
  | Xml.Element.Element name _ rootContent => do
    if name != "Proof_Obligations" then
      throw s!"Unexpected root element {name}"
    let mut infos := (#[] : Array PONameInfo)
    for entry in rootContent do
      match entry with
      | Xml.Content.Element (Xml.Element.Element "Proof_Obligation" _ poContent) =>
        let poTag := (extractTagText poContent).getD s!"po_{infos.size.succ}"
        let mut sgTags := (#[] : Array (Option String))
        for sg in poContent do
          match sg with
          | Xml.Content.Element (Xml.Element.Element "Simple_Goal" _ sgContent) =>
            sgTags := sgTags.push (extractTagText sgContent)
          | _ => pure ()
        infos := infos.push { tag := poTag, goalTags := sgTags }
      | _ => pure ()
    return infos

private def sanitizeIdent (raw : String) : String :=
  let rec sanitizeChars : List Char → Bool → List Char
    | [], _ => []
    | c :: cs, prevUnderscore =>
      let c' := if c.isAlphanum then c else '_'
      let skip := c' == '_' ∧ prevUnderscore
      let nextPrev := c' == '_'
      (if skip then [] else [c']) ++ sanitizeChars cs nextPrev
  let cleaned := String.mk <| sanitizeChars raw.data false
  match cleaned.data with
  | [] => "po"
  | h :: _ => if h.isAlpha then cleaned else "po_" ++ cleaned

private partial def bumpName (used : Std.HashSet String) (candidate : String) (n : Nat) : String :=
  let name := s!"{candidate}_{n}"
  if used.contains name then
    bumpName used candidate (n+1)
  else
    name

private def freshen (used : Std.HashSet String) (candidate : String) : (String × Std.HashSet String) :=
  if used.contains candidate then
    let name := bumpName used candidate 2
    (name, used.insert name)
  else
    (candidate, used.insert candidate)

private def collectSummaries (infos : Array PONameInfo) (pos : List B.ProofObligation) :
    Except String (Array GoalSummary) := do
  let posArr := pos.toArray
  if infos.size != posArr.size then
    throw s!"Mismatch between number of PO tags ({infos.size}) and parsed obligations ({posArr.size})"
  let mut used : Std.HashSet String := Std.HashSet.emptyWithCapacity 32
  let mut summaries := (#[] : Array GoalSummary)
  for ⟨info, po⟩ in Array.zip infos posArr do
    let total := po.goals.length
    let base := sanitizeIdent info.tag
    let tagList := info.goalTags.toList
    for ⟨goalIdx, sg⟩ in List.zip (List.range total) po.goals do
      let candidate := if total = 1 then base else s!"{base}_{goalIdx.succ}"
      let (name, used') := freshen used candidate
      used := used'
      let simpleTag := (tagList.drop goalIdx).head?.bind id
      summaries := summaries.push {
        theoremName := name
        poTag := info.tag
        simpleTag? := simpleTag
        defs := po.defs
        hyps := po.hyps ++ sg.hyps
        goal := sg.goal
        goalIndex := goalIdx.succ
        totalGoals := total
      }
  return summaries

private def renderList (title : String) (items : List B.Term) : List String :=
  match items with
  | [] => [s!"  - {title}: none"]
  | _ => items.map fun t => s!"  - {title}: {t}"

open Std

private def addType (m : RBMap String B.BType compare) (v : String) (τ : B.BType) :=
  match m.find? v with
  | none => m.insert v τ
  | some _ => m

private def elemTypeOfSet : B.BType → Option B.BType
  | .set τ => some τ
  | _ => none

mutual
  private partial def annotateWithType (t : B.Term) (τ : B.BType) (bound : HashSet String) (m : RBMap String B.BType compare) : RBMap String B.BType compare :=
    match t with
    | .var v => if bound.contains v then m else addType m v τ
    | .add x y | .sub x y | .mul x y | .le x y | .eq x y =>
        annotateWithType y τ bound (annotateWithType x τ bound m)
    | .not p => annotateWithType p τ bound m
    | .and x y | .mem x y | .app x y =>
        annotateWithType y τ bound (annotateWithType x τ bound m)
    | .collect _ _ P | .all _ _ P | .lambda _ _ P =>
        annotateWithType P τ bound m
    | _ => m

  private partial def collectVarTypes (t : B.Term) (bound : HashSet String) (m : RBMap String B.BType compare) : RBMap String B.BType compare :=
    match t with
    | .var v => if bound.contains v then m else m
    | .int _ | .bool _ | .ℤ | .𝔹 => m
    | .add x y | .sub x y | .mul x y | .le x y =>
        let m := annotateWithType x .int bound (annotateWithType y .int bound m)
        collectVarTypes y bound (collectVarTypes x bound m)
    | .and x y | .eq x y =>
        collectVarTypes y bound (collectVarTypes x bound m)
    | .not p => collectVarTypes p bound m
    | .mem x S =>
        let m := collectVarTypes S bound m
        let m := collectVarTypes x bound m
        match (B.inferBType S).bind elemTypeOfSet with
        | some τ => annotateWithType x τ bound m
        | none => m
    | .collect vs D P | .all vs D P | .lambda vs D P =>
        let m := collectVarTypes D bound m
        let bound' := vs.foldl (fun b v => b.insert v) bound
        collectVarTypes P bound' m
    | .app f x =>
        collectVarTypes x bound (collectVarTypes f bound m)
    | _ => m
end

private def freeVarTypes (ts : List B.Term) (base : RBMap String B.BType compare := RBMap.empty) : List (String × String) :=
  let m := ts.foldl (fun acc t => collectVarTypes t (HashSet.emptyWithCapacity 8) acc) base
  m.toList.map (fun (v, τ) => (v, τ.toLean))

private def containsSubstr (s sub : String) : Bool :=
  if sub.isEmpty then true else (s.splitOn sub).length > 1

private def renderGoal (globals : HashSet String) (g : GoalSummary) : String :=
  let leanGoal := g.goal.toLeanProp
  let assumptions := (g.defs ++ g.hyps).map (·.toLeanProp)
  let leanObligation := assumptions.foldr (fun h acc => s!"({h}) → {acc}") leanGoal
  let sgTag :=
    match g.simpleTag? with
    | none => ""
    | some t =>
      let trimmed := t.trim
      if trimmed.isEmpty then "" else s!", goal tag `{trimmed}`"
  let header (s : String) : String := s!"/--\nProof obligation `{g.poTag}` goal {g.goalIndex}/{g.totalGoals}{sgTag}.\n{s}\n-/"
  let defs := renderList "defs" g.defs
  let hyps := renderList "hyps" g.hyps
  let goalLine := s!"\n  - goal: {g.goal}"
  let docString := String.intercalate "\n" (defs++hyps) ++ goalLine
  let params :=
    freeVarTypes (g.defs ++ g.hyps ++ [g.goal])
      |>.filter (fun (v, _) => !globals.contains v)
      |>.map (fun (v, ty) => s!"({v} : {ty})")
  let paramStr := if params.isEmpty then "" else " " ++ String.intercalate " " params
  s!"{header docString}\ntheorem {g.theoremName}{paramStr} : {leanObligation} := by\n  sorry\n"

private def renderSection (title sectionName : String) (globals : HashSet String) (gs : List GoalSummary) : String :=
  if gs.isEmpty then "" else
    let header := s!"-- {title}\nsection {sectionName}\n\n"
    let body := String.intercalate "\n" (gs.map (renderGoal globals))
    header ++ body ++ s!"\nend {sectionName}\n"

private def renderFile (mchPath pogPath : FilePath) (summaries : Array GoalSummary) : String :=
  let preamble :=
    s!"/-\nAuto-generated from `{mchPath}`.\nSource POG: `{pogPath}`.\n-/\n\n" ++
    "import Mathlib.Data.Set.Basic\n"
  let terms := summaries.toList.foldl (fun acc g => acc ++ g.defs ++ g.hyps ++ [g.goal]) []
  let baseCtx : RBMap String B.BType compare := RBMap.empty
  let globalParamsRaw := freeVarTypes terms baseCtx
  let globalNames := globalParamsRaw.foldl (fun s (v, _) => s.insert v) (HashSet.emptyWithCapacity 16)
  let globalParams := globalParamsRaw.map (fun (v, ty) => s!"({v} : {ty})")
  let varBlock := if globalParams.isEmpty then "" else "variable " ++ String.intercalate " " globalParams ++ "\n\n"
  let isInit (g : GoalSummary) := containsSubstr g.poTag.toLower "init"
  let hasInv (g : GoalSummary) :=
    containsSubstr g.poTag.toLower "invariant" ||
    containsSubstr ((g.simpleTag?.map String.toLower).getD "") "invariant"
  let init := summaries.toList.filter isInit
  let inv := summaries.toList.filter (fun g => !isInit g && hasInv g)
  let other := summaries.toList.filter (fun g => !isInit g && !hasInv g)
  let sections :=
    [renderSection "Initialisation POs" "Initialisation_POs" globalNames init,
     renderSection "InvariantPreservation POs" "InvariantPreservation_POs" globalNames inv,
     renderSection "Other POs" "Other_POs" globalNames other]
  preamble ++ varBlock ++ String.intercalate "\n" (sections.filter (· ≠ ""))

syntax (name := genPOTheorems) "#pog_thms " str (ppSpace str)? : command

open Elab Command in
elab_rules : command
  | `(command| #pog_thms $mchLit $[$outLit]?) => do
    let some mchStr := Syntax.isStrLit? mchLit | throwError "expected a string literal for the machine path"
    let outStr? :=
      match outLit with
      | some stx => Syntax.isStrLit? stx
      | none => none
    let mch := FilePath.mk mchStr
    let outPath : FilePath :=
      match outStr? with
      | some p => FilePath.mk p
      | none =>
        let base := mch.fileStem.getD (mch.fileName.getD "machine")
        let dir : FilePath := "generated_pog_thms"
        dir / s!"{base}_POs.lean"
    liftIO do
      let pogPath ← mch2pog mch
      let xml ← readPOG pogPath |>.propagateError
      let infos ← IO.ofExcept <| parsePOInfos xml
      let (_, st) ← POGtoB xml |>.run (∅ : DecoderState) |>.propagateError
      let summaries ← IO.ofExcept <| collectSummaries infos st.env.po
      if let some dir := outPath.parent then IO.FS.createDirAll dir
      IO.FS.writeFile outPath (renderFile mch pogPath summaries)
      IO.println s!"Generated {summaries.size} theorem headers at {outPath}"

end B4Lean

#pog_thms "specs/Counter.mch"
