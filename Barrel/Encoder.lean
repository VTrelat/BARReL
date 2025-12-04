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

  private def lookupVar (x : String) : TermElabM Expr := do
    let some e := (← getLCtx).findFromUserName? (.mkStr1 x)
      | throwError "No variable {x} found in context"
    return e.toExpr

  mutual
    partial def makeBinary (f : Name) (t₁ t₂ : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t₁.toExpr, ← t₂.toExpr]

    partial def makeUnary (f : Name) (t : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t.toExpr]

    partial def Syntax.Term.toExpr : Syntax.Term → TermElabM Expr
      | .var v => if v ∈ B.Syntax.reservedIdentifiers then reservedVarToExpr v else lookupVar v
      | .int n => return mkIntLit n
      | .uminus x => makeUnary ``Neg.neg x
      | .le x y => do mkLE (← x.toExpr) (← y.toExpr)
      | .lt x y => do mkLT (← x.toExpr) (← y.toExpr)
      | .bool b => return mkConst (if b then ``True else ``False)
      | .maplet x y => makeBinary ``Prod.mk x y
      | .add x y => do mkAdd (←x.toExpr) (←y.toExpr)
      | .sub x y => do mkSub (←x.toExpr) (←y.toExpr)
      | .mul x y => do mkMul (←x.toExpr) (←y.toExpr)
      | .div x y => makeBinary ``HDiv.hDiv x y -- mkIntDiv <$> x.toExpr <*> y.toExpr
      | .mod x y => makeBinary ``HMod.hMod x y -- mkIntMod <$> x.toExpr <*> y.toExpr
      | .exp x y => makeBinary ``HPow.hPow x y -- do mkIntPowNat <$> x.toExpr <*> mkAppM ``Int.toNat #[← y.toExpr]
      | .and x y => do
        let lam ← withLocalDeclD (← mkFreshUserName `h) (← x.toExpr) λ x ↦
          liftMetaM ∘ mkLambdaFVars #[x] =<< y.toExpr
        mkAppM ``DepAnd #[lam]
      | .or x y => mkOr <$> x.toExpr <*> y.toExpr
      | .imp x y => do
        withLocalDecl (← mkFreshUserName `h) .default (← x.toExpr) λ z ↦
          liftMetaM ∘ mkForallFVars #[z] =<< y.toExpr
      | .iff x y => mkIff <$> x.toExpr <*> y.toExpr
      | .not x => mkNot <$> x.toExpr
      | .eq x y => do mkEq (← x.toExpr) (← y.toExpr)
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
          let xs := xs.map λ (n, t) ↦ (Name.mkStr1 n, t.toExpr)

          withLocalDeclsD (xs.map <| Prod.map id (λ t _ ↦ pure t)) λ xs' ↦ do
            let P ← P.toExpr

            let var₀ ← pure (Match.Pattern.var xs'[0]!.fvarId!, ← inferType xs'[0]!)
            let (pattern, α) ← xs'[1:].foldlM (init := var₀) λ (pat₁, t₁) v ↦ do
              let t₂ ← inferType v
              let t ← mkAppM ``Prod #[t₁, t₂]
              let u₁ ← getDecLevel t₁
              let u₂ ← getDecLevel t₂
              pure (.ctor ``Prod.mk [u₁, u₂] [t₁, t₂] [pat₁, .var v.fvarId!], t)

            -- let ((x₁, …, xₙ), y) := z; ...
            let lhss := [{ ref := .missing
                           fvarDecls := ← xs'.toList.mapM λ v ↦ do pure <| (← getLCtx).findFVar? v |>.get!
                           patterns := [pattern]
                        }]

            let z ← mkFreshUserName `z
            withLocalDeclD z α fun zvec ↦ do
              let D ← mkLambdaFVars xs' P

              let matchType := mkForall `_ .default α <| mkSort 0

              trace[barrel] "lambda motive: {matchType}"

              let matcherResult ← mkMatcher { matcherName := ← mkAuxName `match
                                              matchType
                                              discrInfos := #[{}]
                                              lhss
                                            }
              reportMatcherResultErrors lhss matcherResult
              matcherResult.addMatcher

              trace[barrel] matcherResult.matcher

              let motive ← liftMetaM <| forallBoundedTelescope matchType (.some 1) mkLambdaFVars
              let r := mkAppN matcherResult.matcher #[motive, zvec, D]

              mkLambdaFVars #[zvec] r

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

        -- β is the return type of the function
        let lmvar ← newLMVar
        let β ← newMVar (mkSort <| .succ lmvar)

        let xs := xs.map λ (n, t) ↦ (Name.mkStr1 n, t.toExpr)

        let lam ← withLocalDeclsD (xs.map <| Prod.map id (λ t _ ↦ pure t)) λ xs' ↦ do
          let y ← mkFreshUserName `y
          withLocalDeclD y β fun y' ↦ do
            let var₀ ← pure (Match.Pattern.var xs'[0]!.fvarId!, ← inferType xs'[0]!)
            let (pattern, α) ← xs'[1:].foldlM (init := var₀) λ (pat₁, t₁) v ↦ do
              let t₂ ← inferType v
              let t ← mkAppM ``Prod #[t₁, t₂]
              let u₁ ← getDecLevel t₁
              let u₂ ← getDecLevel t₂
              pure (.ctor ``Prod.mk [u₁, u₂] [t₁, t₂] [pat₁, .var v.fvarId!], t)

            let P ← P.toExpr
            let D ← liftMetaM ∘ mkLambdaFVars (xs'.push y') =<< withLocalDeclD (← mkFreshUserName `h) P λ P ↦ do
              let F ← F.toExpr
              assignMVar β (← inferType F)
              mkAppM ``DepAnd #[← mkLambdaFVars #[P] (← mkEq y' F)]

            let β ← instantiateMVars β

            let levelα ← getDecLevel α
            let γ := mkApp2 (mkConst ``Prod [levelα, lmvar]) α β

            let pattern : Match.Pattern := .ctor ``Prod.mk [levelα, lmvar] [α, β] [pattern, .var y'.fvarId!]

            -- let ((x₁, …, xₙ), y) := z; ...
            let lhss := [{ ref := .missing
                           fvarDecls := ← (xs'.push y').toList.mapM λ v ↦ do pure <| (← getLCtx).findFVar? v |>.get!
                           patterns := [pattern]
                        }]

            let z ← mkFreshUserName `z
            withLocalDeclD z γ fun zvec ↦ do
              let matchType := mkForall `_ .default γ <| mkSort 0

              trace[barrel] "lambda motive: {matchType}"

              let matcherResult ← mkMatcher { matcherName := ← mkAuxName `match
                                              matchType
                                              discrInfos := #[{}]
                                              lhss
                                            }
              reportMatcherResultErrors lhss matcherResult
              matcherResult.addMatcher

              trace[barrel] matcherResult.matcher

              let motive ← liftMetaM <| forallBoundedTelescope matchType (.some 1) mkLambdaFVars
              let r := mkAppN matcherResult.matcher #[motive, zvec, D]

              mkLambdaFVars #[zvec] r

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
