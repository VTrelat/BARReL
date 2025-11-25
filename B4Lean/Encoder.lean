import B.Environment
import B4Lean.Meta

open Std Lean Meta Elab Term

namespace B

def BType.toExpr : BType → Expr
  | .int => Int.mkType
  | .bool => .sort .zero
  | .set α => mkApp (.const ``Set [0]) (α.toExpr)
  | .prod α β => mkApp2 (.const ``Prod [0, 0]) α.toExpr β.toExpr

private def newMVar (type? : Option Lean.Expr) : MetaM Expr := do
  -- let mvar ← pure Int.mkType
  let mvar ← Meta.mkFreshExprMVar type?
  trace[b4lean.pog] "New metavariable {mvar}"
  return mvar

private def newLMVar : MetaM Level := do
  let lmvar ← Meta.mkFreshLevelMVar
  trace[b4lea.pog] "New level metavariable {lmvar}"
  return lmvar

private partial def getSetElemType (ty : Expr) : MetaM Expr := do
  let rec loop (t : Expr) (didWhnf : Bool) : MetaM Expr := do
    match t with
    | .app (.const ``Set _) α => pure α
    | .forallE n dom body bi =>
        Meta.withLocalDecl n bi dom fun x => do
          let body' := body.instantiate1 x
          if (← Meta.isProp body') then
            return dom
          else if didWhnf then
            throwError "Expected a set type, got {t}"
          else
            loop (← Meta.whnf t) true
    | _ =>
        let t' ← Meta.whnf t
        if didWhnf || t' == t then
          throwError "Expected a set type, got {t}"
        else
          loop t' true
  loop ty false

private partial def flattenProdType (ty : Expr) : MetaM (List Expr) := do
  let ty ← Meta.whnf ty
  match ty with
  | .app (.app (.const ``Prod _) α) β =>
      return (← flattenProdType α) ++ (← flattenProdType β)
  | _ => return [ty]

private partial def mkProdTuple : List Expr → MetaM Expr
  | [] => throwError "mkProdTuple: empty tuple"
  | [x] => pure x
  | x :: xs => do
      let tail ← mkProdTuple xs
      mkAppM ``Prod.mk #[x, tail]

partial def Term.toExpr : Term → TermElabM Expr
  | .var v =>
    match v with
    | _ => do
      let some e := (← getLCtx).findFromUserName? (.mkStr1 v)
        | throwError "No variable {v} found in context"
      return e.toExpr
  | .int n => return mkIntLit n
  | .le x y => mkIntLE <$> x.toExpr <*> y.toExpr
  | .bool b =>
    return .const (if b then ``True else ``False) []
  | .maplet x y =>
    mkApp2 (.const ``Prod.mk [0, 0]) <$> (x.toExpr) <*> (y.toExpr)
  | .add x y => mkIntAdd <$> (x.toExpr) <*> (y.toExpr)
  | .sub x y => mkIntSub <$> (x.toExpr) <*> (y.toExpr)
  | .mul x y => mkIntMul <$> (x.toExpr) <*> (y.toExpr)
  | .and x y => mkAnd <$> (x.toExpr) <*> (y.toExpr)
  | .or x y => mkOr <$> (x.toExpr) <*> (y.toExpr)
  | .imp x y => mkForall `_ .default <$> x.toExpr <*> y.toExpr
  | .not x => mkNot <$> (x.toExpr)
  | .eq x y => do
    let x' ← x.toExpr
    let y' ← y.toExpr
    liftMetaM <| mkEq x' y'
  | .mem x S => do
    let S' ← S.toExpr
    let x' ← x.toExpr
    let elemTy ← liftMetaM <| getSetElemType (← Meta.inferType S')
    let xTy ← liftMetaM <| Meta.inferType x'
    unless (← liftMetaM <| Meta.isDefEq xTy elemTy) do
      throwError "Type mismatch in membership: {x} has type {xTy}, expected {elemTy}"
    return mkApp S' x'
  | .ℤ => return mkApp (.const ``Set.univ [0]) Int.mkType
  | .𝔹 => return mkApp (.const ``Set.univ [0]) (.sort 0)
  | .collect xs D P => do
    let m? ← newMVar (.some <| .sort 1)
    let x ← mkFreshUserName `x
    mkApp2 (.const ``setOf [0]) m?
      <$> withLocalDeclD x m? fun xvec ↦ do
        trace[b4lean.pog] "Collect: generating new variable `{xvec}` for `setOf`"

        let rec f : List 𝒱 → TermElabM Expr
          | [] => do
            -- xs' = (x₁, ..., (xₙ₋₁, xₙ))
            let ⟨mτ?, xs'⟩ ← do
              let mτ₁? ← newMVar (.some <| .sort 1)
              let some e := (← getLCtx).findFromUserName? (.mkStr1 xs.getLast!)
                | throwError "No variable {xs.getLast!} found in context"
              xs.reverse.tail!.foldrM (init := (mτ₁?, e.toExpr)) fun xᵢ (mτ₂?, acc) ↦ do
                let mτ₁? : Expr ← newMVar (.some <| .sort 1)
                let some e := (← getLCtx).findFromUserName? (.mkStr1 xᵢ)
                  | throwError "No variable {xs.getLast!} found in context"
                return (
                  mkApp2 (.const ``Prod [0, 0]) mτ₁? mτ₂?,
                  mkApp4 (.const ``Prod.mk [0, 0]) mτ₁? mτ₂? e.toExpr acc
                )
            -- x̄ ∈ D
            let memD : Expr :=
              mkApp5
                (.const ``Membership.mem [0, 0])
                mτ?
                (mkApp (.const ``Set [0]) mτ?)
                (mkApp (.const ``Set.instMembership [0]) mτ?)
                (← D.toExpr) xvec
            -- x̄ = xs'
            let lmvar ← newLMVar
            let eq : Expr := mkApp3 (.const ``Eq [lmvar]) mτ? xvec xs'

            -- x̄ = xs' ∧ x̄ ∈ D ∧ P[x̄/vs]
            return mkAndN [eq, memD, ← P.toExpr]
          | x :: xs => do
            let mτ? ← newMVar (.some <| .sort 1)

            mkApp2 (Expr.const ``Exists [1]) mτ?
              <$> withLocalDeclD (Name.mkStr1 x) mτ? fun y =>
                (liftMetaM ∘ mkLambdaFVars #[y] =<< f xs)

        trace[b4lean.pog] "Enclosing lambda for `setOf` (bound var: {xvec})"
        liftMetaM ∘ mkLambdaFVars #[xvec] =<< f xs

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

  let rec f : List (Σ (_ : 𝒱), BType) → Array Expr → TermElabM Expr
    | [], vars => do
      let g ← goal.toExpr
      let g ← liftMetaM <| mkForallFVars vars g
      synthesizeSyntheticMVarsNoPostponing
      let g ← instantiateMVars g
      let g ← Term.ensureHasType (.some <| .sort 0) g
      -- Meta.check g
      dbg_trace g
      return g
    | ⟨x, τ⟩ :: xs, vars =>
      Meta.withLocalDeclD (Name.mkStr1 x) τ.toExpr fun v ↦ f xs (vars.push v)

  f Γ.entries #[]


open Term Elab

def ProofObligation.mkGoal (po : ProofObligation) (Γ : TypeContext) : TermElabM (List Expr) :=
  po.goals.mapM (fun sg => {sg with hyps := po.defs ++ po.hyps ++ sg.hyps}.mkGoal Γ)

def Env.mkGoal (E : B.Env) : TermElabM (List (String × Expr)) :=
  List.flatten <$> E.po.traverse fun po => ((po.name, ·) <$> ·) <$> po.mkGoal E.context

end B
