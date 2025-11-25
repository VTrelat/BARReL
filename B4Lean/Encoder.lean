import B.Environment
import B4Lean.Meta

open Std Lean Meta Elab Term

namespace B

def BType.toExpr : BType → Expr
  | .int => Int.mkType
  | .bool => .sort .zero
  | .set α => mkApp (.const ``Set [0]) (α.toExpr)
  | .prod α β => mkApp2 (.const ``Prod [0, 0]) α.toExpr β.toExpr

private def newMVar : MetaM Expr := do
  let mvar ← mkMVarEx <$> mkFreshMVarId
  trace[b4lean.pog] "New metavariable {mvar}"
  return mvar

private def newLMVar : MetaM Level := do
  let lmvar ← mkLevelMVarEx <$> mkFreshLMVarId
  trace[b4lea.pog] "New level metavariable {lmvar}"
  return lmvar

partial def Term.toExpr (vs : HashMap String Expr) : Term → TermElabM Expr
  | .var v =>
    match v with
    | _ => return vs.get! v
  | .int n => return mkIntLit n
  | .le x y => mkIntLE <$> x.toExpr vs <*> y.toExpr vs
  | .bool b =>
    return .const (if b then ``True else ``False) []
  | .maplet x y =>
    mkApp2 (.const ``Prod.mk [0, 0]) <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .add x y => mkIntAdd <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .sub x y => mkIntSub <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .mul x y => mkIntMul <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .and x y => mkAnd <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .or x y => mkOr <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .imp x y => mkForall `_ .default <$> x.toExpr vs <*> y.toExpr vs
  | .not x => mkNot <$> (x.toExpr vs)
  | .eq x y => do
    let lmvar ← mkLevelMVar <$> mkFreshLMVarId
    let mvar ← mkMVarEx <$> mkFreshMVarId
    mkApp3 (Expr.const ``Eq [lmvar]) mvar <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .mem x S => do
    let mτ₁? ← newMVar
    mkApp5
      (.const ``Membership.mem [0, 0])
      mτ₁?
      (mkApp (.const ``Set [0]) mτ₁?)
      (mkApp (.const ``Set.instMembership [0]) mτ₁?)
      <$> (S.toExpr vs)
      <*> (x.toExpr vs)
  | .ℤ => return mkApp (.const ``Set.univ [0]) Int.mkType
  | .𝔹 => return mkApp (.const ``Set.univ [0]) (.sort 0)
  | .collect xs D P => do
    -- let xs' := xs.map vs.get!
    -- mkCollect xs' D P vs
    let m? ← newMVar
    let x ← mkFreshUserName `x
    mkApp2 (.const ``setOf [0]) m?
      <$> withLocalDeclD x m? fun xvec ↦ do
        trace[b4lean.pog] "Collect: generating new variable `{xvec}` for `setOf`"

        let rec f (vs : HashMap String Expr) : List 𝒱 → TermElabM Expr
          | [] => do
            -- xs' = (x₁, ..., (xₙ₋₁, xₙ))
            let ⟨mτ?, xs'⟩ ← do
              let mτ₁? ← newMVar
              xs.reverse.tail!.foldrM (init := (mτ₁?, vs.get! xs.getLast!)) fun xᵢ (mτ₂?, acc) ↦ do
                let mτ₁? : Expr ← newMVar
                return (
                  mkApp2 (.const ``Prod [0, 0]) mτ₁? mτ₂?,
                  mkApp4 (.const ``Prod.mk [0, 0]) mτ₁? mτ₂? (vs.get! xᵢ) acc
                )
            -- x̄ ∈ D
            let memD : Expr :=
              mkApp5
                (.const ``Membership.mem [0, 0])
                mτ?
                (mkApp (.const ``Set [0]) mτ?)
                (mkApp (.const ``Set.instMembership [0]) mτ?)
                (← D.toExpr vs) xvec
            -- x̄ = xs'
            let lmvar ← newLMVar
            let eq : Expr := mkApp3 (.const ``Eq [lmvar]) mτ? xvec xs'

            -- x̄ = xs' ∧ x̄ ∈ D ∧ P[x̄/vs]
            return mkAndN [eq, memD, ← P.toExpr vs]
          | x :: xs => do
            let mτ? ← newMVar

            mkApp2 (Expr.const ``Exists [1]) mτ?
              <$> withLocalDeclD (Name.mkStr1 x) mτ? fun y =>
                (liftMetaM ∘ mkLambdaFVars #[y] =<< f (vs.insert x y) xs)

        trace[b4lean.pog] "Enclosing lambda for `setOf` (bound var: {xvec})"
        liftMetaM ∘ mkLambdaFVars #[xvec] =<< f vs xs

  | .pow S => panic! "not implemented"
  | .cprod S T => panic! "not implemented"
  | .union S T => panic! "not implemented"
  | .inter S T => panic! "not implemented"
  | .card S => panic! "not implemented"
  | .app f x => panic! "not implemented"
  | .lambda vs D P => panic! "not implemented"
  | .pfun A B => panic! "not implemented"
  | .min S => panic! "not implemented"
  | .max S => panic! "not implemented"
  | .all vs D P => panic! "not implemented"

def SimpleGoal.mkGoal (sg : SimpleGoal) (Γ : TypeContext) : TermElabM Expr := do
  let goal : Term := sg.hyps.foldr (fun t acc => t ⇒ᴮ acc) sg.goal

  dbg_trace "Encoding {goal}"

  let rec f : HashMap String Expr → List (Σ (_ : 𝒱), BType) → TermElabM Expr
    | map, [] => do
      let g ← goal.toExpr map
      let g ← liftMetaM <| mkForallFVars map.values.toArray g
      synthesizeSyntheticMVarsNoPostponing
      let g ← instantiateMVars g
      let g ← Term.ensureHasType (.some <| .sort 0) g
      -- Meta.check g
      dbg_trace g
      return g
    | map, ⟨x, τ⟩ :: xs =>
      Meta.withLocalDeclD (Name.mkStr1 x) τ.toExpr fun v ↦
        f (map.insert x v) xs

  f ∅ Γ.entries


open Term Elab

def ProofObligation.mkGoal (po : ProofObligation) (Γ : TypeContext) : TermElabM (List Expr) :=
  -- TODO:FIXME: handle defs
  po.goals.mapM (fun sg => {sg with hyps := po.defs ++ po.hyps ++ sg.hyps}.mkGoal Γ)

def Env.mkGoal (E : B.Env) : TermElabM (List (String × Expr)) :=
  List.flatten <$> E.po.traverse fun po => ((po.name, ·) <$> ·) <$> po.mkGoal E.context

end B
