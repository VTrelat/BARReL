-- import B.Environment
import POGReader_.Basic
import B4Lean.Meta
import B4Lean.Builtins

open Std Lean Meta Elab Term

namespace B

def varIsReserved : String → Prop
  | "NAT" | "NAT1" | "NATURAL" | "NATURAL1"
  | "INT"
  | "FLOAT"
  | "REAL"
    => True
  | _ => False

instance : DecidablePred varIsReserved := by
  intro v
  unfold varIsReserved
  split <;>
  first
  | exact instDecidableTrue
  | exact instDecidableFalse

open Lean Elab Builtins

def reservedVarToExpr : String → TermElabM Lean.Expr
  | "NAT" => return mkConst ``NAT
  | "NAT1" => return mkConst ``NAT1
  | "NATURAL" => return mkConst ``NATURAL
  | "NATURAL1" => return mkConst ``NATURAL1
  | "INT" => return mkConst ``INT
  | v => throwError "Variable {v} is not reserved."

def Syntax.Typ.toExpr : Typ → Expr
  | .int => Int.mkType
  | .bool => .sort .zero
  | .real => mkConst ``Real
  | .pow α => mkApp (.const ``Set [0]) (α.toExpr)
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

private partial def flattenProdType : Expr → Nat → MetaM (List Expr)
  | .app (.app (.const ``Prod _) α) β, n + 1 => do
      return (←flattenProdType α n).concat β
  | ty, _ + 1 => throwError "Expected a product type, got {ty}"
  | ty, 0 => return [ty]

private partial def mkProdTuple : List Expr → MetaM Expr
  | [] => throwError "mkProdTuple: empty tuple"
  | [x] => pure x
  | x :: xs => do
      let tail ← mkProdTuple xs
      mkAppM ``Prod.mk #[x, tail]

private def lookupVar (x : 𝒱) : TermElabM Expr := do
  let some e := (← getLCtx).findFromUserName? (.mkStr1 x)
    | throwError "No variable {x} found in context"
  return e.toExpr

partial def Syntax.Term.toExpr : B.Syntax.Term → TermElabM Expr
  | .var v =>
    -- match v with
    -- | _ => lookupVar v
    if varIsReserved v then
      reservedVarToExpr v
    else
      lookupVar v
  | .num n ty => return mkIntLit n
  | .le x y => mkIntLE <$> x.toExpr <*> y.toExpr
  | .lt x y => mkIntLT <$> x.toExpr <*> y.toExpr
  | .bool b =>
    return .const (if b then ``True else ``False) []
  | .maplet x y => do
    let x ← x.toExpr
    let y ← y.toExpr
    mkAppM ``Prod.mk #[x, y]
  | .add x y => mkIntAdd <$> x.toExpr <*> y.toExpr
  | .sub x y => mkIntSub <$> x.toExpr <*> y.toExpr
  | .mul x y => mkIntMul <$> x.toExpr <*> y.toExpr
  | .and x y => mkAnd <$> x.toExpr <*> y.toExpr
  | .or x y => mkOr <$> x.toExpr <*> y.toExpr
  | .imp x y => mkForall `_ .default <$> x.toExpr <*> y.toExpr
  | .not x => mkNot <$> x.toExpr
  | .eq x y => do
    let x' ← x.toExpr
    let y' ← y.toExpr
    liftMetaM <| mkEq x' y'
  | .mem x S => do
    let S' ← S.toExpr
    let x' ← x.toExpr
    mkAppM ``Membership.mem #[S', x']
  | .𝔹 => return mkApp (mkConst ``Set.univ [0]) (.sort 0)
  | .ℤ => return mkApp (mkConst ``Set.univ [0]) Int.mkType
  | .ℝ => return mkApp (mkConst ``Set.univ [0]) (mkConst ``Real)
  | .collect xs P => do
    let x ← mkFreshBinderName

    let τs := xs.map (·.snd.toExpr)
    -- α = (α₁ × …) × αₙ
    let α ← τs.pop.foldrM (init := τs.back!) fun τᵢ acc ↦ mkAppM ``Prod #[τᵢ, acc]


    let lam ← withLocalDeclD x α fun xvec ↦ do

      let rec collect_aux : List (String × Syntax.Typ) → TermElabM Expr
        | [] => do
          -- xs' = (x₁, ..., (xₙ₋₁, xₙ))
          let xs' ← do
            xs.pop.foldrM (init := ← lookupVar xs.back!.fst) fun ⟨xᵢ, _⟩ acc ↦ do
              mkAppM ``Prod.mk #[← lookupVar xᵢ, acc]
          -- x̄ = xs'
          let eq : Expr ← mkEq xvec xs'
          -- x̄ = xs' ∧ P[x̄/vs]
          return mkAnd eq (← P.toExpr)
        | ⟨x, t⟩ :: xs => do
          let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
            (liftMetaM ∘ mkLambdaFVars #[y] =<< collect_aux xs)
          mkAppM ``Exists #[lam]

      liftMetaM ∘ mkLambdaFVars #[xvec] =<< collect_aux xs.toList

    mkAppM ``setOf #[lam]
  -- | .interval lo hi => do
  --   let lo' ← lo.toExpr
  --   let hi' ← hi.toExpr
  --   mkAppM ``Builtins.interval #[lo', hi']
  | .all xs P => do
    let x ← mkFreshBinderName

    let τs := xs.map (·.snd.toExpr)
    -- α = (α₁ × …) × αₙ
    let α ← τs.pop.foldrM (init := τs.back!) fun τᵢ acc ↦ mkAppM ``Prod #[τᵢ, acc]

    let lam ← withLocalDeclD x α fun xvec ↦ do

      let rec all_aux : List (String × Syntax.Typ) → TermElabM Expr
        | [] => do
          -- xs' = (x₁, ..., (xₙ₋₁, xₙ))
          let xs' ← do
            xs[:xs.size-2].foldrM (init := ← lookupVar xs.back!.fst) fun ⟨xᵢ, _⟩ acc ↦ do
              mkAppM ``Prod.mk #[← lookupVar xᵢ, acc]
          -- x̄ = xs'
          let eq : Expr ← mkEq xvec xs'
          -- x̄ = xs' → P[x̄/vs]
          return mkForall `_ .default eq (← P.toExpr)
        | ⟨x, t⟩ :: xs => do
          let lam ← withLocalDeclD (Name.mkStr1 x) t.toExpr fun y =>
            (liftMetaM ∘ mkForallFVars #[y] =<< all_aux xs)
          return lam

      liftMetaM ∘ mkForallFVars #[xvec] =<< all_aux xs.toList

    return lam
  | .set xs => panic! "not implemented (set)"
  | .pow S => panic! "not implemented (pow)"
  | .cprod S T => panic! "not implemented (cprod)"
  | .union S T => panic! "not implemented (union)"
  | .inter S T => panic! "not implemented (inter)"
  | .card S => panic! "not implemented (card)"
  | .app f x => panic! "not implemented (app)"
  | .lambda vs D P => panic! "not implemented (lambda)"
  | .pfun A B => panic! "not implemented (pfun)"
  | .tfun A B => panic! "not implemented (tfun)"
  -- | .tfun A B => panic! "not implemented (pfun)"
  | .min S => panic! "not implemented (min)"
  | .max S => panic! "not implemented (max)"
  | .exists vs P => panic! "not implemented (exists)"

-- def BType.toTerm' : BType → TermElabM Lean.Term
--   | .int => `(Int)
--   | .bool => `(Prop)
--   | .set α => do `(Set $(← α.toTerm'))
--   | .prod α β => do `($(← α.toTerm') × $(← β.toTerm'))

-- partial def Term.toTerm : Term → TermElabM Lean.Term
--   | .var v => pure ⟨mkIdent (.mkStr1 v)⟩
--   | .int n =>
--     `(($(if n < 0 then
--       Syntax.mkApp (mkIdent `«term-_») #[⟨mkNode numLitKind #[mkAtom (-n).repr]⟩]
--     else
--       ⟨mkNode numLitKind #[mkAtom n.repr]⟩) : ℤ))
--   | .bool b => return if b then mkIdent ``True else mkIdent ``False
--   | .maplet x y => do `(($(← x.toTerm), $(← y.toTerm)))
--   | .add x y => do `($(← x.toTerm) + $(← y.toTerm))
--   | .sub x y => do `($(← x.toTerm) - $(← y.toTerm))
--   | .mul x y => do `($(← x.toTerm) * $(← y.toTerm))
--   | .le x y => do `($(← x.toTerm) ≤ $(← y.toTerm))
--   | .and x y => do `($(← x.toTerm) ∧ $(← y.toTerm))
--   | .or x y => do `($(← x.toTerm) ∨ $(← y.toTerm))
--   | .imp x y => do `($(← x.toTerm) → $(← y.toTerm))
--   | .not x => do `(¬ $(← x.toTerm))
--   | .eq x y => do `($(← x.toTerm) = $(← y.toTerm))
--   | .ℤ => do `(@Set.univ Int)
--   | .𝔹 => do `(@Set.univ Bool)
--   | .mem x S => do `($(← x.toTerm) ∈ $(← S.toTerm))
--   | .collect vs D P => do
--     let vs : List Name := vs.map Name.mkStr1
--     let vs' : List Lean.Term := vs.map (⟨mkIdent ·⟩)
--     let rec f (x : Ident) : List Name → TermElabM Lean.Term := fun
--       | [] => do
--         let vs'' : Lean.Term ← vs'.dropLast.foldrM (init := vs'.getLast!) λ v acc ↦ `(($v, $acc))
--         `($x = $vs'' ∧ $x ∈ $(← D.toTerm) ∧ $(← P.toTerm))
--       | n :: ns => do
--         let n : TSyntax `Lean.Parser.Term.funBinder := mkIdent n
--         `(Exists λ $n ↦ $(← f x ns))

--     let y ← mkFreshBinderName
--     -- `(term| {x | ∃ vs…. x = (vs…) ∧ x ∈ $(← D.toTerm) ∧ $(← P.toTerm)})
--     `({ $(mkIdent y):ident | $(← f (mkIdent y) vs) })
--   | .pow S => panic! "a"
--   | .cprod S T => panic! "b"
--   | .union S T => panic! "c"
--   | .inter S T => panic! "d"
--   | .card S => panic! "e"
--   | .app f x => panic! "f"
--   | .lambda vs D P => panic! "g"
--   | .pfun A B => panic! "h"
--   | .min S => panic! "i"
--   | .max S => panic! "j"
--   | .all vs D P => panic! "k"

def POG.Goal.toExpr (sg : POG.Goal) : TermElabM Expr := do
  let goal : Syntax.Term := sg.hyps.foldr (fun t acc => .imp t acc) sg.goal

  trace[b4lean.pog] s!"Encoding: {repr goal}"

  let vars : Array (Name × (Array Expr → TermElabM Expr)) :=
    sg.vars.map λ ⟨x, τ⟩ ↦ ⟨.mkStr1 x, λ _ ↦ pure τ.toExpr⟩
  Meta.withLocalDeclsD vars λ vars ↦ do
    let g ←
      goal.toExpr
        >>= liftMetaM ∘ mkForallFVars vars (usedOnly := true)
        >>= Term.ensureHasType (.some <| .sort 0)
    trace[b4lean.pog] m!"Pre-check goal: {indentExpr g}"
    Meta.check g
    let g ← instantiateMVars g
    Meta.liftMetaM g.ensureHasNoMVars
    return g

-- open Term Elab

-- def ProofObligation.mkGoal (po : ProofObligation) (Γ : TypeContext) : TermElabM (List Expr) :=
--   po.goals.mapM (fun sg => {sg with hyps := po.defs ++ po.hyps ++ sg.hyps}.mkGoal Γ)

-- def Env.mkGoal (E : B.Env) : TermElabM (List (String × Expr)) :=
--   List.flatten <$> E.po.traverse fun po => ((po.name, ·) <$> ·) <$> po.mkGoal E.context

end B
