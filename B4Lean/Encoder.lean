import POGReader.Basic
import B4Lean.Meta
import B4Lean.Builtins

open Std Lean Meta Elab Term

namespace B
  open Lean Elab

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
    trace[barrel.pog] "New metavariable {mvar}"
    return mvar

  private def assignMVar (β ty : Expr) : MetaM PUnit := do
    if !(← β.mvarId!.isAssigned) && (← Meta.isDefEq (← β.mvarId!.getType) (← inferType ty)) then
      trace[barrel.pog] m!"Assigning metavariable {β} to {ty}"
      β.mvarId!.assign ty

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



  def WFHypotheses := Std.HashMap Expr Expr × Std.HashMap Expr Expr
  -- variable (hyps : IO.Ref WFHypotheses)

  private def newHypothesis (hyps : IO.Ref WFHypotheses) (h : Expr) (thm : Expr) : TermElabM PUnit := do
    trace[barrel.pog] "Generating new WF hypothesis {h} : {thm}"

    let hypsMap ← hyps.get
    if hypsMap.1.contains h then throwError s!"Hypothesis {repr h} already exists"
    let thm ← Meta.ensureHasType thm <| mkSort 0
    hyps.set (hypsMap.1.insert h thm, hypsMap.2.insert thm h)

  private def makeWFHypothesis (hyps : IO.Ref WFHypotheses) (wf : Expr) (k : Expr → MetaM Expr) : TermElabM Expr := do
    let hypsMap ← hyps.get
    let h ←
      if let .some var := hypsMap.2.get? wf then
        pure var
      else
        let h ← mkFVar <$> mkFreshFVarId
        newHypothesis hyps h wf
        pure h
    withLCtx ((← getLCtx).mkLocalDecl h.fvarId! `wf wf) (← getLocalInstances) do
      k h

  def checkpoint {α} /-[ToMessageData α]-/ (t : IO.Ref WFHypotheses → TermElabM α) (k : α → TermElabM Expr) : TermElabM Expr := do
    let rec mkWfHyps (g : Expr) : List (Expr × Expr) → TermElabM Expr
      | [] => pure g
      | ⟨x, t⟩ :: xs => do
        let lctx := (← getLCtx).mkLocalDecl x.fvarId! `wf t
        withLCtx lctx (← getLocalInstances) do
          mkAppM ``Exists #[← liftMetaM ∘ mkLambdaFVars #[x] =<< mkWfHyps g xs]

    let wfHyps ← IO.mkRef ⟨∅, ∅⟩
    let t ← t wfHyps
    -- if !(← wfHyps.get).1.isEmpty then
    --   trace[barrel.pog] m!"Inserting some WF hypotheses before {t}"
    mkWfHyps (← k t) (← wfHyps.get).1.toList

  mutual
    partial def makeBinder (xs : Array (String × Syntax.Typ)) (P : Syntax.Term)
      (mkBinder : Array Expr → Expr → MetaM Expr) (mkHyp : Expr → MetaM Expr) (mkConcl : Expr → Expr → Expr) :
        TermElabM Expr := do
      if xs.size = 1 then
        let ⟨x, t⟩ := xs[0]!

        withLocalDeclD (Name.mkStr1 x) t.toExpr λ xvec ↦
          liftMetaM ∘ mkBinder #[xvec] =<< checkpoint P.toExpr pure
      else
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
              return mkConcl eq (← checkpoint P.toExpr pure)
            | ⟨x, t⟩ :: xs => do
              let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
                (liftMetaM ∘ mkBinder #[y] =<< go xs)
              mkHyp lam

          liftMetaM ∘ mkBinder #[xvec] =<< go xs.toList

    partial def makeBinary (hyps : IO.Ref WFHypotheses) (f : Name) (t₁ t₂ : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t₁.toExpr hyps, ← t₂.toExpr hyps]

    partial def makeUnary (hyps : IO.Ref WFHypotheses) (f : Name) (t : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t.toExpr hyps]

    partial def Syntax.Term.toExpr (hyps : IO.Ref WFHypotheses) : Syntax.Term → TermElabM Expr
      | .var v => if v ∈ B.Syntax.reservedIdentifiers then reservedVarToExpr v else lookupVar v
      | .int n => return mkIntLit n
      | .uminus x => mkIntNeg <$> x.toExpr hyps
      | .le x y => mkIntLE <$> x.toExpr hyps <*> y.toExpr hyps
      | .lt x y => mkIntLT <$> x.toExpr hyps <*> y.toExpr hyps
      | .bool b => return mkConst (if b then ``True else ``False)
      | .maplet x y => makeBinary hyps ``Prod.mk x y
      | .add x y => mkIntAdd <$> x.toExpr hyps <*> y.toExpr hyps
      | .sub x y => mkIntSub <$> x.toExpr hyps <*> y.toExpr hyps
      | .mul x y => mkIntMul <$> x.toExpr hyps <*> y.toExpr hyps
      | .div x y => mkIntDiv <$> x.toExpr hyps <*> y.toExpr hyps
      | .mod x y => mkIntMod <$> x.toExpr hyps <*> y.toExpr hyps
      | .exp x y => do mkIntPowNat <$> x.toExpr hyps <*> mkAppM ``Int.toNat #[← y.toExpr hyps]
      | .and x y =>
        checkpoint (Functor.map mkAnd ∘ x.toExpr) λ x ↦
          x <$> checkpoint y.toExpr pure
      | .or x y => mkOr <$> x.toExpr hyps <*> y.toExpr hyps
      | .imp x y =>
        checkpoint (Functor.map (mkForall `_  .default) ∘ x.toExpr) λ x ↦
          checkpoint y.toExpr λ y ↦
            pure <| x y
      | .iff x y => mkIff <$> checkpoint x.toExpr pure <*> checkpoint y.toExpr pure
      | .not x => mkNot <$> x.toExpr hyps
      | .eq x y => do
        let x' ← x.toExpr hyps
        let y' ← y.toExpr hyps
        liftMetaM <| mkEq x' y'
      | .mem x S => makeBinary hyps ``Membership.mem S x
      | .𝔹 => mkAppOptM ``Set.univ #[mkSort 0]
      | .ℤ => mkAppOptM ``Set.univ #[Int.mkType]
      | .ℝ => mkAppOptM ``Set.univ #[mkConst ``Real]
      | .collect xs P => do
        mkAppM ``setOf #[← makeBinder xs P mkLambdaFVars (mkAppM ``Exists #[·]) mkAnd]
      | .all xs P => do
        makeBinder xs P mkForallFVars pure <| mkForall `_ .default
      | .exists xs P => do
        mkAppM ``Exists #[← makeBinder xs P mkLambdaFVars (mkAppM ``Exists #[·]) mkAnd]
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
              let F ← checkpoint F.toExpr pure

              assignMVar β (← inferType F)
              let β ← instantiateMVars β

              let P ← checkpoint P.toExpr pure

              let y ← mkFreshBinderName
              let lam ← withLocalDeclD y β fun y ↦ do
                let xs' ← do
                  xs[1:].foldlM (init := ← lookupVar xs[0]!.fst) fun acc ⟨xᵢ, _⟩ ↦ do
                    mkAppM ``Prod.mk #[acc, ← lookupVar xᵢ]
                -- x̄ = (xs', y)
                let eq : Expr ← mkEq zvec (mkApp4 (mkConst ``Prod.mk [levelα, lmvar]) α β xs' y)
                -- y = F[x̄/xs']
                let eqF : Expr ← mkEq y F
                -- x̄ = (xs', y) ∧ P[x̄/xs'] ∧ y = F[x̄/xs']
                mkLambdaFVars #[y] <| mkAndN [eq, P, eqF]
              mkAppM ``Exists #[lam]
            | ⟨x, t⟩ :: xs => do
              let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
                (liftMetaM ∘ mkLambdaFVars #[y] =<< go xs)
              mkAppM ``Exists #[lam]

          liftMetaM ∘ mkLambdaFVars #[zvec] =<< go xs.toList
        mkAppM ``setOf #[lam]
      | .interval lo hi => makeBinary hyps ``Builtins.interval lo hi
      | .subset S T => makeBinary hyps ``HasSubset.Subset S T
      | .set es ty => do
        if es.isEmpty then
          mkAppOptM ``EmptyCollection.emptyCollection #[ty.toExpr, .none]
        else
          let emp ← mkAppOptM ``Singleton.singleton #[.none, ty.toExpr, .none, ← es.back!.toExpr hyps]
          es.pop.foldrM (init := emp) fun e acc ↦ do mkAppM ``Insert.insert #[←e.toExpr hyps, acc]
      | .setminus S T => makeBinary hyps ``SDiff.sdiff S T
      | .pow S => makeUnary hyps ``Set.powerset S
      | .pow₁ S => makeUnary hyps ``Builtins.POW₁ S
      | .cprod S T => makeBinary hyps ``SProd.sprod S T
      | .union S T => makeBinary hyps ``Union.union S T
      | .inter S T => makeBinary hyps ``Inter.inter S T
      | .rel A B => makeBinary hyps ``B.Builtins.rels A B
      | .image R X => makeBinary hyps ``SetRel.image R X
      | .inv R => makeUnary hyps ``SetRel.inv R
      | .id A => makeUnary hyps ``B.Builtins.id A
      | .dom f => makeUnary hyps ``B.Builtins.dom f
      | .ran f => makeUnary hyps ``B.Builtins.ran f
      | .domRestr R E => makeBinary hyps ``B.Builtins.domRestr E R
      | .domSubtr R E => makeBinary hyps ``B.Builtins.domSubtr E R
      | .codomRestr R E => makeBinary hyps ``B.Builtins.codomRestr R E
      | .codomSubtr R E => makeBinary hyps ``B.Builtins.codomSubtr R E
      | .fun A B isPartial =>
        makeBinary hyps (if isPartial then ``B.Builtins.pfun else ``B.Builtins.tfun) A B
      | .injfun A B isPartial => do
        makeBinary hyps (if isPartial then ``B.Builtins.injPFun else ``B.Builtins.injTFun) A B
      | .surjfun A B isPartial => do
        makeBinary hyps (if isPartial then ``B.Builtins.surjPFun else ``B.Builtins.surjTFun) A B
      | .bijfun A B isPartial => do
        makeBinary hyps (if isPartial then ``B.Builtins.bijPFun else ``B.Builtins.bijTFun) A B
      | .min S => do
        let S ← S.toExpr hyps
        let wf ← mkAppM ``B.Builtins.min.WF #[S]
        makeWFHypothesis hyps wf λ h ↦ mkAppM ``B.Builtins.min #[S, h]
      | .max S => do
        let S ← S.toExpr hyps
        let wf ← mkAppM ``B.Builtins.max.WF #[S]
        makeWFHypothesis hyps wf λ h ↦ mkAppM ``B.Builtins.max #[S, h]
      | .app f x => do
        let f ← f.toExpr hyps
        let x ← x.toExpr hyps
        let wf ← mkAppM ``B.Builtins.app.WF #[f, x]
        makeWFHypothesis hyps wf λ h ↦ mkAppM ``B.Builtins.app #[f, x, h]
      | .fin S => makeUnary hyps ``B.Builtins.FIN S
      | .fin₁ S => makeUnary hyps ``B.Builtins.FIN₁ S
      | .card S => panic! "not implemented (card)"
  end

  def POG.Goal.toExpr (sg : POG.Goal) : TermElabM Expr := do
    -- trace[barrel.pog] s!"Encoding: {goal}"

    let vars : Array (Name × (Array Expr → TermElabM Expr)) :=
      sg.vars.map λ ⟨x, τ⟩ ↦ ⟨.mkStr1 x, λ _ ↦ pure τ.toExpr⟩

    Meta.withLocalDeclsD vars λ vars ↦ do
      -- let rec goHyp : List Syntax.Term → TermElabM Expr
      --   | [] => checkpoint sg.goal.toExpr pure
      --   | t :: ts => checkpoint t.toExpr λ t ↦ mkForall `_ .default t <$> goHyp ts

      trace[barrel.pog] "Decoded goal: {sg.goal}"

      let g ← checkpoint sg.goal.toExpr pure

      trace[barrel.pog] "Generated goal (no quantified variable): {indentExpr g}"

      let g ← liftMetaM (mkForallFVars vars (usedOnly := true) g)
              >>= Term.ensureHasType (.some <| .sort 0)
      Meta.check g
      let g ← instantiateMVars g
      Meta.liftMetaM g.ensureHasNoMVars
      return g

end B
