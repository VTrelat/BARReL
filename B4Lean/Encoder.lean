import B.Environment
namespace B

open Std Lean

def BType.toExpr : BType → Expr
  | .int => Expr.const ``Int []
  | .bool => Expr.const ``Bool []
  | .set α => Expr.app (Expr.const ``Set []) (α.toExpr)
  | .prod α β => Expr.app (Expr.app (Expr.const ``Prod []) α.toExpr) β.toExpr

def Term.toExpr (vs : HashMap String Expr): Term → Expr
  | .int n =>
    if n >= 0 then
      Expr.lit (Literal.natVal n.toNat)
    else
      panic! "not implemented"
      -- Expr.app (.const ?? []) (Literal.natVal (-n).toNat)
  | .le x y => panic! "not implemented"
  | .var v => vs.get! v
  | .bool b => panic! "not implemented"
  | .maplet x y => panic! "not implemented"
  | .add x y => panic! "not implemented"
  | .sub x y => panic! "not implemented"
  | .mul x y => panic! "not implemented"
  | .and x y => panic! "not implemented"
  | .not x => panic! "not implemented"
  | .eq x y => panic! "not implemented"
  | .ℤ => panic! "not implemented"
  | .𝔹 => panic! "not implemented"
  | .mem x S => panic! "not implemented"
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
    | map, [] => Meta.mkForallFVars map.values.toArray (goal.toExpr map)
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
