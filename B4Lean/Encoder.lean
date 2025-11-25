import B.Environment

open Std Lean Meta

namespace B

def BType.toExpr : BType → Expr
  | .int => .const ``Int []
  | .bool => .sort .zero
  | .set α => mkApp (.const ``Set []) (α.toExpr)
  | .prod α β => mkApp2 (.const ``Prod []) α.toExpr β.toExpr

partial def Term.toExpr (vs : HashMap String Expr) : Term → MetaM Expr
  | .var v =>
    match v with
    | _ => return vs.get! v
  | .int n => return mkIntLit n
  | .le x y => mkIntLE <$> x.toExpr vs <*> y.toExpr vs
  | .bool b =>
    return .const (if b then ``True else ``False) []
  | .maplet x y =>
    mkApp2 (Expr.const ``Prod.mk [0, 0]) <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .add x y => mkIntAdd <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .sub x y => mkIntSub <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .mul x y => mkIntMul <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .and x y => mkAnd <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .or x y => mkOr <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .imp x y => panic! "not implemented"
  | .not x => mkNot <$> (x.toExpr vs)
  | .eq x y => do
    let mvar ← mkMVarEx <$> mkFreshMVarId
    mkApp3 (Expr.const ``Eq [0]) mvar <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .mem x S => do
    let mτ? ← mkMVarEx <$> mkFreshMVarId
    mkApp5
      (.const ``Membership.mem [0, 0])
      mτ?
      (mkApp (.const ``Set [0]) mτ?)
      (mkApp (.const ``Set.instMembership [0]) mτ?)
      <$> (S.toExpr vs) <*> (x.toExpr vs)
  | .ℤ => return mkApp (.const ``Set.univ [0]) Int.mkType
  | .𝔹 => return mkApp (.const ``Set.univ [0]) (.sort 0)
  | .collect xs D P => do
    -- let xs' := xs.map vs.get!
    -- mkCollect xs' D P vs
    let m? ← mkMVarEx <$> mkFreshMVarId
    let m?₂ ← mkMVarEx <$> mkFreshMVarId
    mkApp2 (.const ``setOf [0]) m?₂
      <$> withLocalDeclD `x m? fun xvec ↦ do
        let rec f (vs : HashMap String Expr) : List 𝒱 → MetaM Expr
          | [] => do
            -- xs' = (x₁, ..., (xₙ₋₁, xₙ))
            let xs' : Expr ←
              xs.reverse.tail!.foldrM (init := vs.get! xs.getLast!) fun xᵢ acc ↦ do
                let mτ₁? : Expr ← mkMVarEx <$> mkFreshMVarId
                let mτ₂? : Expr ← mkMVarEx <$> mkFreshMVarId
                return mkApp4 (Expr.const ``Prod.mk [0, 0]) mτ₁? mτ₂? (vs.get! xᵢ) acc
            -- meta-var for the type of x̄
            let mτ? : Expr ← mkMVarEx <$> mkFreshMVarId
            -- x̄ ∈ D
            let memD : Expr :=
              mkApp5
                (.const ``Membership.mem [0, 0])
                mτ?
                (mkApp (.const ``Set [0]) mτ?)
                (mkApp (.const ``Set.instMembership [0]) mτ?)
                (←D.toExpr vs) xvec
            -- x̄ = xs'
            let eq : Expr := mkApp3 (Expr.const ``Eq [0]) mτ? xvec xs'

            -- x̄ = xs' ∧ x̄ ∈ D ∧ P[x̄/vs]
            return mkAndN [eq, memD, ←P.toExpr vs]
          | x :: xs => do
            let mτ? ← mkMVarEx <$> mkFreshMVarId

            withLocalDecl (Name.mkStr1 x) .default mτ? fun y => do
              let body ← f (vs.insert x y) xs
              mkApp2 (Expr.const ``Exists [1]) mτ? <$> mkLambdaFVars #[y] body

        mkLambdaFVars #[xvec] (←f vs xs)

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

def SimpleGoal.mkGoal (sg : SimpleGoal) (Γ : TypeContext) : MetaM Expr := do
  let goal : Term := sg.hyps.foldr (fun t acc => t ⇒ᴮ acc) sg.goal

  dbg_trace "Encoding {goal}"

  let rec f : HashMap String Expr → List (Σ (_ : 𝒱), BType) → MetaM Expr
    | map, [] => do Meta.mkForallFVars map.values.toArray (←goal.toExpr map)
    | map, ⟨x, τ⟩ :: xs =>
      Meta.withLocalDeclD (Name.mkStr1 x) τ.toExpr fun v ↦
        f (map.insert x v) xs

  f ∅ Γ.entries

open Term Elab

def ProofObligation.mkGoal (po : ProofObligation) (Γ : TypeContext): MetaM (List Expr) :=
  -- TODO:FIXME: handle defs
  po.goals.mapM (fun sg => {sg with hyps := po.defs ++ po.hyps ++ sg.hyps}.mkGoal Γ)

def Env.mkGoal (E : B.Env) : MetaM (List (String × Expr)) :=
  List.flatten <$> E.po.traverse fun po => ((po.name, ·) <$> ·) <$> po.mkGoal E.context

end B
