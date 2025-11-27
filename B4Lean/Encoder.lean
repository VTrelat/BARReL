import POGReader.Basic
import B4Lean.Meta
import B4Lean.Builtins

open Std Lean Meta Elab Term

namespace B
  open Lean Elab

  def reservedVarToExpr : (k : String) → k ∈ B.Syntax.reservedIdentifiers → TermElabM Lean.Expr
    | "NAT", _ => return mkConst ``Builtins.NAT
    | "NAT1", _ => return mkConst ``Builtins.NAT₁
    | "NATURAL", _ => return mkConst ``Builtins.NATURAL
    | "NATURAL1", _ => return mkConst ``Builtins.NATURAL₁
    | "INT", _ => return mkConst ``Builtins.INT
    | "INTEGER", _ => return mkConst ``Builtins.INTEGER
    | "BOOL", _ => return mkConst ``Builtins.BOOL
    | "FLOAT", _ => return mkConst ``Builtins.FLOAT
    | "REAL", _ => return mkConst ``Builtins.REAL
    | v, _ => throwError "Variable {v} is not reserved."

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

  private def lookupVar (x : String) : TermElabM Expr := do
    let some e := (← getLCtx).findFromUserName? (.mkStr1 x)
      | throwError "No variable {x} found in context"
    return e.toExpr

  mutual
    partial def makeBinder (xs : Array (String × Syntax.Typ)) (P : Syntax.Term)
      (mkBinder : Array Expr → Expr → MetaM Expr) (mkHyp : Expr → MetaM Expr) (mkConcl : Expr → Expr → Expr) :
        TermElabM Expr := do
      let x ← mkFreshBinderName

      -- α = (α₁ × …) × αₙ
      let α ← xs[1:].foldlM (init := xs[0]!.snd.toExpr) fun acc ⟨_, τᵢ⟩ ↦ do
        mkAppM ``Prod #[acc, τᵢ.toExpr]

      withLocalDeclD x α fun xvec ↦ do
        let rec go : List (String × Syntax.Typ) → TermElabM Expr
          | [] => do
            let xs' ← do
              xs[1:].foldlM (init := ← lookupVar xs[0]!.fst) fun acc ⟨xᵢ, _⟩ ↦ do
                mkAppM ``Prod.mk #[acc, ← lookupVar xᵢ]
            -- x̄ = xs'
            let eq : Expr ← mkEq xvec xs'
            -- x̄ = xs' ∧ P[x̄/vs]
            return mkConcl eq (← P.toExpr)
          | ⟨x, t⟩ :: xs => do
            let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
              (liftMetaM ∘ mkBinder #[y] =<< go xs)
            mkHyp lam

        liftMetaM ∘ mkBinder #[xvec] =<< go xs.toList

    partial def Syntax.Term.toExpr : B.Syntax.Term → TermElabM Expr
      | .var v => if h : v ∈ B.Syntax.reservedIdentifiers then reservedVarToExpr v h else lookupVar v
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
        mkAppM ``setOf #[← makeBinder xs P mkLambdaFVars (mkAppM ``Exists #[·]) mkAnd]
      | .all xs P => do
        makeBinder xs P mkForallFVars pure <| mkForall `_ .default
      | .exists xs P => do
        mkAppM ``Exists #[← makeBinder xs P mkLambdaFVars (mkAppM ``Exists #[·]) mkAnd]
      | .interval lo hi => do
        let lo' ← lo.toExpr
        let hi' ← hi.toExpr
        mkAppM ``Builtins.interval #[lo', hi']
      | .set es ty => do
        let emp ← mkAppOptM ``EmptyCollection.emptyCollection #[.some ty.toExpr, .none]
        es.foldrM (init := emp) fun e acc ↦ do mkAppM ``Insert.insert #[←e.toExpr, acc]
      | .pow S => do
        let S ← S.toExpr
        mkAppM ``Builtins.POW #[S]
      | .pow₁ S => do
        let S ← S.toExpr
        mkAppM ``Builtins.POW₁ #[S]
      | .cprod S T => do
        let S ← S.toExpr
        let T ← T.toExpr
        mkAppM ``Builtins.cprod #[S, T]
      | .union S T => panic! "not implemented (union)"
      | .inter S T => panic! "not implemented (inter)"
      | .rel A B => do
        let A ← A.toExpr
        let B ← B.toExpr
        mkAppM ``B.Builtins.rels #[A, B]
      | .app f x => do
        let f ← f.toExpr
        let x ← x.toExpr
        mkAppM ``B.Builtins.app #[f, x]
      | .lambda vs D P => panic! "not implemented (lambda)"
      | .fun A B isPartial => do
        let A ← A.toExpr
        let B ← B.toExpr
        mkAppM (if isPartial then ``B.Builtins.pfun else ``B.Builtins.tfun) #[A, B]
      | .injfun A B isPartial => do
        let A ← A.toExpr
        let B ← B.toExpr
        mkAppM (if isPartial then ``B.Builtins.injPFun else ``B.Builtins.injTFun) #[A, B]
      | .min S => panic! "not implemented (min)"
      | .max S => panic! "not implemented (max)"
      | .card S => panic! "not implemented (card)"
  end

  def POG.Goal.toExpr (sg : POG.Goal) : TermElabM Expr := do
    let goal : Syntax.Term := sg.hyps.foldr (fun t acc => .imp t acc) sg.goal

    trace[b4lean.pog] s!"Encoding: {goal}"

    let vars : Array (Name × (Array Expr → TermElabM Expr)) :=
      sg.vars.map λ ⟨x, τ⟩ ↦ ⟨.mkStr1 x, λ _ ↦ pure τ.toExpr⟩
    Meta.withLocalDeclsD vars λ vars ↦ do
      let g ←
        goal.toExpr
          >>= liftMetaM ∘ mkForallFVars vars (usedOnly := true)
          >>= Term.ensureHasType (.some <| .sort 0)
      Meta.check g
      let g ← instantiateMVars g
      Meta.liftMetaM g.ensureHasNoMVars
      return g

end B
