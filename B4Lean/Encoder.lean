import B.Environment
namespace B

open Std Lean

def BType.toExpr : BType → Expr
  | .int => .const ``Int []
  | .bool => .sort .zero
  | .set α => mkApp (.const ``Set []) (α.toExpr)
  | .prod α β => mkApp2 (.const ``Prod []) α.toExpr β.toExpr

def Term.toExpr (vs : HashMap String Expr) : Term → MetaM Expr
  | .var v => return vs.get! v
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
  | .not x => mkNot <$> (x.toExpr vs)
  | .eq x y => do
    let mvar ← mkMVarEx <$> mkFreshMVarId
    mkApp3 (Expr.const ``Eq [0]) mvar <$> (x.toExpr vs) <*> (y.toExpr vs)
  | .mem x S => do
    let mvar ← mkMVarEx <$> mkFreshMVarId
    mkApp5
      (.const ``Membership.mem [0, 0])
      mvar
      (mkApp (.const ``Set []) mvar)
      (.const ``Set.instMembership [0])
      <$> (S.toExpr vs) <*> (x.toExpr vs)
  | .ℤ => return mkApp (.const ``Set.univ [0]) Int.mkType
  | .𝔹 => return mkApp (.const ``Set.univ [0]) (.sort 0)
  | .collect vs D P => panic! "not implemented"
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

  let rec f : HashMap String Expr → List (Sigma (fun _:𝒱 ↦ BType)) → MetaM Expr
    | map, [] => do Meta.mkForallFVars map.values.toArray (←goal.toExpr map)
    | map, ⟨x, τ⟩ :: xs =>
      Meta.withLocalDecl (Name.mkStr1 x) .default τ.toExpr fun v ↦
        f (map.insert x v) xs
  f ∅ Γ.entries

open Term Elab

def ProofObligation.mkGoal (po : ProofObligation) (Γ : TypeContext): MetaM (List Expr) :=
  -- TODO:FIXME: handle defs
  po.goals.mapM (fun sg => {sg with hyps := po.hyps ++ sg.hyps}.mkGoal Γ)

def Env.mkGoal (E : B.Env) : MetaM (List (String × Expr)) :=
  List.flatten <$> E.po.traverse fun po => ((po.name, ·) <$> ·) <$> po.mkGoal E.context

end B
