import POGReader.Basic
import Barrel.Meta
import Barrel.Builtins

open Std Lean Meta Elab Term

namespace B

  def reservedVarToExpr : (k : String) → TermElabM Lean.Expr
    | "MININT", _ => return mkConst ``Builtins.MININT
    | "MAXINT", _ => return mkConst ``Builtins.MAXINT
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
    trace[barrel] "New metavariable {mvar}"
    return mvar

  private def assignMVar (β ty : Expr) : MetaM PUnit := do
    if !(← β.mvarId!.isAssigned) && (← Meta.isDefEq (← β.mvarId!.getType) (← inferType ty)) then
      trace[barrel] m!"Assigning metavariable {β} to {ty}"
      β.mvarId!.assign ty

  private def newLMVar : MetaM Level := do
    let lmvar ← Meta.mkFreshLevelMVar
    trace[barrel] "New level metavariable {lmvar}"
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

  partial def _root_.Lean.Expr.getForallHeads : Lean.Expr → List Lean.Expr
    | .forallE _ t b _ => t :: b.getForallHeads
    | .mdata _ b => b.getForallHeads
    | _ => []

  private def _root_.Lean.Meta.mkUnaryOp (className : Name) (opName : Name) (a : Expr) : MetaM Expr := do
    let aType ← inferType a
    let u ← getDecLevel aType
    let inst ← synthInstance (mkApp (mkConst className [u]) aType)
    return mkApp3 (mkConst opName [u]) aType inst a

  private def _root_.Lean.Meta.mkNeg (a : Expr) : MetaM Expr := Lean.Meta.mkUnaryOp ``Neg ``Neg.neg a

  mutual
    partial def makeBinary (f : Name) (t₁ t₂ : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t₁.toExpr, ← t₂.toExpr]

    partial def makeUnary (f : Name) (t : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t.toExpr]

    partial def Syntax.Term.toExpr : Syntax.Term → TermElabM Expr
      | .var v => if v ∈ B.Syntax.reservedIdentifiers then reservedVarToExpr v else lookupVar v
      | .int n => return mkIntLit n
      | .uminus x => do mkNeg (←x.toExpr)
      | .le x y => do mkLE (← x.toExpr) (← y.toExpr)
      | .lt x y => do mkLT (← x.toExpr) (← y.toExpr)
      | .bool b => return mkConst (if b then ``True else ``False)
      | .maplet x y => makeBinary ``Prod.mk x y
      | .add x y => do mkAdd (←x.toExpr) (←y.toExpr)
      | .sub x y => do mkSub (←x.toExpr) (←y.toExpr)
      | .mul x y => do mkMul (←x.toExpr) (←y.toExpr)
      | .div x y => mkIntDiv <$> x.toExpr <*> y.toExpr
      | .mod x y => mkIntMod <$> x.toExpr <*> y.toExpr
      | .exp x y => do mkIntPowNat <$> x.toExpr <*> mkAppM ``Int.toNat #[← y.toExpr]
      | .and x y => do
        let w ← mkFreshUserName `h
        let x ← x.toExpr
        let lam ← withLocalDeclD w x λ x ↦
          liftMetaM ∘ mkLambdaFVars #[x] =<< y.toExpr
        mkAppM ``DepAnd #[lam]
      | .or x y => mkOr <$> x.toExpr <*> y.toExpr
      | .imp x y => do
        withLocalDecl (← mkFreshBinderName) .default (← x.toExpr) λ z ↦
          liftMetaM ∘ mkForallFVars #[z] =<< y.toExpr
      | .iff x y =>
        mkIff <$> x.toExpr
              <*> y.toExpr
      | .not x => mkNot <$> x.toExpr
      | .eq x y => do
        let x ← x.toExpr
        let y ← y.toExpr
        liftMetaM <| mkEq x y
      | .mem x S => makeBinary ``Membership.mem S x
      | .𝔹 => mkAppOptM ``Set.univ #[mkSort 0]
      | .ℤ => mkAppOptM ``Set.univ #[Int.mkType]
      | .ℝ => mkAppOptM ``Set.univ #[mkConst ``Real]
      | .collect xs P => do
        let lam ← if xs.size = 1 then
          let ⟨x, t⟩ := xs[0]!

          withLocalDeclD (Name.mkStr1 x) t.toExpr λ xvec ↦
            liftMetaM ∘ mkLambdaFVars #[xvec] =<< P.toExpr
        else
          let x ← mkFreshBinderName

          -- α = (α₁ × …) × αₙ
          let α ← xs[1:].foldlM (init := xs[0]!.snd.toExpr) fun acc ⟨_, τᵢ⟩ ↦ do
            mkAppM ``Prod #[acc, τᵢ.toExpr]

          withLocalDeclD x α fun xvec ↦ do
            let rec go_collect : List (String × Syntax.Typ) → TermElabM Expr
              | [] => do
                let xs' ← do
                  xs[1:].foldlM (init := ← lookupVar xs[0]!.fst) fun acc ⟨xᵢ, _⟩ ↦ do
                    mkAppM ``Prod.mk #[acc, ← lookupVar xᵢ]
                -- x̄ = xs'
                let eq : Expr ← mkEq xvec xs'
                -- x̄ = xs' ∧ P[x̄/vs]
                let lam ← withLocalDeclD (← mkFreshBinderName) eq λ eq ↦
                  liftMetaM ∘ mkLambdaFVars #[eq] =<< P.toExpr
                mkAppM ``DepAnd #[lam]
              | ⟨x, t⟩ :: xs => do
                let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y ↦ do
                  (liftMetaM ∘ mkLambdaFVars #[y] =<< go_collect xs)
                mkAppM ``Exists #[lam]

            liftMetaM ∘ mkLambdaFVars #[xvec] =<< go_collect xs.toList

        mkAppM ``setOf #[lam]
      | .all xs P => do
        let rec go_forall : List (String × Syntax.Typ) → TermElabM Expr
          | [] => P.toExpr
          | ⟨x, t⟩ :: xs => do
            withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y ↦ do
              (liftMetaM ∘ mkForallFVars #[y] =<< go_forall xs)

        go_forall xs.toList
      | .exists xs P => do
        let rec go_exists : List (String × Syntax.Typ) → TermElabM Expr
          | [] => P.toExpr
          | ⟨x, t⟩ :: xs => do
            let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y ↦ do
              (liftMetaM ∘ mkLambdaFVars #[y] =<< go_exists xs)
            mkAppM ``Exists #[lam]

        go_exists xs.toList
      | .lambda xs P F => do
        -- { z | ∃ x₁ … xₙ, ∃ y, z = ((x₁, …, xₙ), y) ∧ D ∧ y = F }

        -- α = (α₁ × …) × αₙ
        let α ← xs[1:].foldlM (init := xs[0]!.snd.toExpr) fun acc ⟨_, τᵢ⟩ ↦ do
          mkAppM ``Prod #[acc, τᵢ.toExpr]
        let levelα ← getDecLevel α

        -- β is the return type of the function
        let lmvar ← newLMVar
        let β ← newMVar (mkSort <| .succ lmvar)

        let γ := mkApp2 (mkConst ``Prod [levelα, lmvar]) α β

        let z ← mkFreshBinderName
        let lam ← withLocalDeclD z γ fun zvec ↦ do
          let rec go : List (String × Syntax.Typ) → TermElabM Expr
            | [] => do
              let y ← mkFreshBinderName
              let lam ← withLocalDeclD y β fun y ↦ do
                -- compute return type of F: this consumes F already
                let _ ← assignMVar β (← inferType (← F.toExpr))
                let β ← instantiateMVars β

                let xs' ← do
                  xs[1:].foldlM (init := ← lookupVar xs[0]!.fst) fun acc ⟨xᵢ, _⟩ ↦ do
                    mkAppM ``Prod.mk #[acc, ← lookupVar xᵢ]
                -- x̄ = (xs', y)
                let eq : Expr ← mkEq zvec (mkApp4 (mkConst ``Prod.mk [levelα, lmvar]) α β xs' y)
                -- y = F[x̄/xs']
                -- let eqF : Expr ← mkEq y F
                -- x̄ = (xs', y) ∧ P[x̄/xs'] ∧ y = F[x̄/xs']

                let n₁ ← mkFreshUserName `h₁
                let n₂ ← mkFreshUserName `h₂
                let lam ← withLocalDeclD n₁ eq λ eq ↦
                  liftMetaM ∘ mkLambdaFVars #[eq] =<< do
                    withLocalDeclD n₂ (← P.toExpr) λ P ↦ do
                      let eq' ← mkEq y (←F.toExpr) -- no other choice
                      mkAppM ``DepAnd #[←liftMetaM <| mkLambdaFVars #[P] eq']

                mkLambdaFVars #[y] (← mkAppM ``DepAnd #[lam])
              mkAppM ``Exists #[lam]
            | ⟨x, t⟩ :: xs => do
              let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
                (liftMetaM ∘ mkLambdaFVars #[y] =<< go xs)
              mkAppM ``Exists #[lam]

          liftMetaM ∘ mkLambdaFVars #[zvec] =<< go xs.toList
        mkAppM ``setOf #[lam]
      | .interval lo hi => makeBinary ``Builtins.interval lo hi
      | .subset S T => makeBinary ``HasSubset.Subset S T
      | .set es ty => do
        if es.isEmpty then
          mkAppOptM ``EmptyCollection.emptyCollection #[ty.toExpr, .none]
        else
          let emp ← mkAppOptM ``Singleton.singleton #[.none, ty.toExpr, .none, ← es.back!.toExpr]
          es.pop.foldrM (init := emp) fun e acc ↦ do mkAppM ``Insert.insert #[←e.toExpr, acc]
      | .setminus S T => makeBinary ``SDiff.sdiff S T
      | .pow S => makeUnary ``Set.powerset S
      | .pow₁ S => makeUnary ``Builtins.POW₁ S
      | .cprod S T => makeBinary ``SProd.sprod S T
      | .union S T => makeBinary ``Union.union S T
      | .inter S T => makeBinary ``Inter.inter S T
      | .rel A B => makeBinary ``B.Builtins.rels A B
      | .image R X => makeBinary ``SetRel.image R X
      | .inv R => makeUnary ``SetRel.inv R
      | .id A => makeUnary ``B.Builtins.id A
      | .dom f => makeUnary ``B.Builtins.dom f
      | .ran f => makeUnary ``B.Builtins.ran f
      | .domRestr R E => makeBinary ``B.Builtins.domRestr E R
      | .domSubtr R E => makeBinary ``B.Builtins.domSubtr E R
      | .codomRestr R E => makeBinary ``B.Builtins.codomRestr R E
      | .codomSubtr R E => makeBinary ``B.Builtins.codomSubtr R E
      | .fun A B isPartial =>
        makeBinary (if isPartial then ``B.Builtins.pfun else ``B.Builtins.tfun) A B
      | .injfun A B isPartial => do
        makeBinary (if isPartial then ``B.Builtins.injPFun else ``B.Builtins.injTFun) A B
      | .surjfun A B isPartial => do
        makeBinary (if isPartial then ``B.Builtins.surjPFun else ``B.Builtins.surjTFun) A B
      | .bijfun A B isPartial => do
        makeBinary (if isPartial then ``B.Builtins.bijPFun else ``B.Builtins.bijTFun) A B
      | .min S => do
        let S ← S.toExpr
        let wfMVar ← liftMetaM ∘ newMVar =<< mkAppM ``B.Builtins.min.WF #[S]
        mkAppM ``B.Builtins.min #[S, wfMVar]
      | .max S => do
        let S ← S.toExpr
        let wfMVar ← liftMetaM ∘ newMVar =<< mkAppM ``B.Builtins.max.WF #[S]
        mkAppM ``B.Builtins.max #[S, wfMVar]
      | .app f x => do
        let f ← f.toExpr
        let x ← x.toExpr
        let wfMVar ← liftMetaM ∘ newMVar =<< mkAppM ``B.Builtins.app.WF #[f, x]
        mkAppM ``B.Builtins.app #[f, x, wfMVar]
      | .fin S => makeUnary ``B.Builtins.FIN S
      | .fin₁ S => makeUnary ``B.Builtins.FIN₁ S
      | .card S => do
        let S ← S.toExpr
        let wfMVar ← liftMetaM ∘ newMVar =<< mkAppM ``B.Builtins.card.WF #[S]
        mkAppM ``B.Builtins.card #[S, wfMVar]

  end

  def POG.Goal.toExpr (sg : POG.Goal) : TermElabM (Expr × Array (Expr × MVarId)) := do
    -- trace[barrel.pog] s!"Encoding: {goal}"

    let vars : Array (Name × (Array Expr → TermElabM Expr)) :=
      sg.vars.map λ ⟨x, τ⟩ ↦ ⟨.mkStr1 x, λ _ ↦ pure τ.toExpr⟩

    let g ← Meta.withLocalDeclsD vars λ vars ↦ do
      -- let rec goHyp : List Syntax.Term → TermElabM Expr
      --   | [] => checkpoint sg.goal.toExpr pure
      --   | t :: ts => checkpoint t.toExpr λ t ↦ mkForall `_ .default t <$> goHyp ts

      trace[barrel] "Decoded goal: {sg.goal}"

      let g ← sg.goal.toExpr

      trace[barrel] "Generated goal (no quantified variable): {indentExpr g}"

      let g ← liftMetaM (mkForallFVars vars (usedOnly := true) g)
              >>= Term.ensureHasType (.some <| .sort 0)
      Meta.check g
      instantiateMVars g

    let mvars := g.collectMVars {} |>.result

    trace[barrel] "Generated goal: {indentExpr g}"

    let mut wfs := #[]
    let mut i := 0

    for mvar in mvars do
      let ty ← mvar.withContext do
        liftMetaM ∘ mkForallFVars (← getLCtx).getFVars =<< mvar.getType

      trace[barrel.wf] "WF metavariable to solve {sg.name}.wf_{(i : Nat)} (?{mvar.name}):{indentExpr ty}"

      wfs := wfs.push (ty, mvar)

    return (g, wfs)

end B
