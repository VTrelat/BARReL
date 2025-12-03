import POGReader.Basic
import Barrel.Meta
import Barrel.Builtins

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



  inductive WFQuantifier | all | ex

  instance : ToString WFQuantifier where
    toString | .all => "∀" | .ex => "∃"

  def WFQuantifier.invert : WFQuantifier → WFQuantifier
    | .all => .ex
    | .ex => .all

  structure WFHypotheses where
    fvars : Array Expr
    fvarsToThm : Std.HashMap Expr Expr
    thmToFvars : Std.HashMap Expr Expr
  -- variable (hyps : IO.Ref WFHypotheses)

  private def newHypothesis (hyps : IO.Ref WFHypotheses) (h : Expr) (thm : Expr) : TermElabM PUnit := do
    trace[barrel.pog] "Generating new WF hypothesis {h} : {thm}"

    let hypsMap ← hyps.get
    if hypsMap.1.contains h then throwError s!"Hypothesis {repr h} already exists"
    let thm ← Meta.ensureHasType thm <| mkSort 0
    hyps.set {
      fvars := hypsMap.fvars.push h
      fvarsToThm := hypsMap.fvarsToThm.insert h thm
      thmToFvars := hypsMap.thmToFvars.insert thm h
    }

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

  def checkpoint (tag : String) (quant : WFQuantifier)
    (t : WFQuantifier → IO.Ref WFHypotheses → TermElabM Expr) (k : Expr → TermElabM Expr) :
      TermElabM Expr := do
    let rec mkWfHyps (g : Expr) : List (Expr × Expr) → TermElabM Expr
      | [] => pure g
      | ⟨x, t⟩ :: xs => do
        let lctx := (← getLCtx).mkLocalDecl x.fvarId! `wf t
        withLCtx lctx (← getLocalInstances) do
          match quant with
          | .ex => mkAppM ``Exists #[← liftMetaM ∘ mkLambdaFVars #[x] =<< mkWfHyps g xs]
          | .all => liftMetaM ∘ mkForallFVars #[x] =<< mkWfHyps g xs

    trace[barrel.checkpoints] m!"Checkpoint @{tag} (quant := {quant})!"

    trace[barrel.checkpoints] m!"Checkpoint @{tag}!"

    let wfHyps ← IO.mkRef ⟨∅, ∅, ∅⟩
    let t' ← t quant wfHyps

    let hypsMap ← wfHyps.get
    let hasWF := !hypsMap.fvars.isEmpty

    if hasWF then
      trace[barrel.pog] m!"Inserting {(← wfHyps.get).fvars.size} WF hypotheses before {indentExpr t'}"

    let t ← k =<< mkWfHyps t' (hypsMap.fvars.map λ v ↦ (v, hypsMap.fvarsToThm.get! v)).toList

    if hasWF then
      trace[barrel.pog] m!"  Finished term: {t}"
    return t


  mutual
    partial def makeBinder (quant : WFQuantifier) (xs : Array (String × Syntax.Typ)) (P : Syntax.Term)
      (mkBinder : Array Expr → Expr → MetaM Expr) (mkHyp : Expr → MetaM Expr) (mkConcl : Expr → Expr → Expr) :
        TermElabM Expr := do
      if xs.size = 1 then
        let ⟨x, t⟩ := xs[0]!

        withLocalDeclD (Name.mkStr1 x) t.toExpr λ xvec ↦
          liftMetaM ∘ mkBinder #[xvec] =<< checkpoint "binder:in" quant P.toExpr pure
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
              return mkConcl eq (← checkpoint "binder:in" quant P.toExpr pure)
            | ⟨x, t⟩ :: xs => do
              let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
                (liftMetaM ∘ mkBinder #[y] =<< go xs)
              mkHyp lam

          liftMetaM ∘ mkBinder #[xvec] =<< go xs.toList

    partial def makeBinary (quant : WFQuantifier) (hyps : IO.Ref WFHypotheses) (f : Name) (t₁ t₂ : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t₁.toExpr quant hyps, ← t₂.toExpr quant hyps]

    partial def makeUnary (quant : WFQuantifier) (hyps : IO.Ref WFHypotheses) (f : Name) (t : Syntax.Term) : TermElabM Expr := do
      mkAppM f #[← t.toExpr quant hyps]

    partial def Syntax.Term.toExpr (quant : WFQuantifier) (hyps : IO.Ref WFHypotheses) : Syntax.Term → TermElabM Expr
      | .var v => if v ∈ B.Syntax.reservedIdentifiers then reservedVarToExpr v else lookupVar v
      | .int n => return mkIntLit n
      | .uminus x => mkIntNeg <$> x.toExpr quant hyps
      | .le x y => mkIntLE <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .lt x y => mkIntLT <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .bool b => return mkConst (if b then ``True else ``False)
      | .maplet x y => makeBinary quant hyps ``Prod.mk x y
      | .add x y => mkIntAdd <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .sub x y => mkIntSub <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .mul x y => mkIntMul <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .div x y => mkIntDiv <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .mod x y => mkIntMod <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .exp x y => do mkIntPowNat <$> x.toExpr quant hyps <*> mkAppM ``Int.toNat #[← y.toExpr quant hyps]
      | .and x y => mkAnd <$> x.toExpr quant hyps <*> checkpoint "and:right" quant y.toExpr pure
      | .or x y => mkOr <$> x.toExpr quant hyps <*> y.toExpr quant hyps
      | .imp x y =>
        checkpoint "imp:right" quant y.toExpr λ y ↦ do
          pure <| mkForall `_  .default (← x.toExpr quant.invert hyps) y
      | .iff x y =>
        mkIff <$> checkpoint "iff:left" quant x.toExpr pure
              <*> checkpoint "iff:right" quant y.toExpr pure
      | .not x => mkNot <$> x.toExpr quant hyps
      | .eq x y => do
        let x ← x.toExpr quant hyps
        let y ← y.toExpr quant hyps
        liftMetaM <| mkEq x y
      | .mem x S => makeBinary quant hyps ``Membership.mem S x
      | .𝔹 => mkAppOptM ``Set.univ #[mkSort 0]
      | .ℤ => mkAppOptM ``Set.univ #[Int.mkType]
      | .ℝ => mkAppOptM ``Set.univ #[mkConst ``Real]
      | .collect xs P => do
        mkAppM ``setOf #[← makeBinder quant xs P mkLambdaFVars (mkAppM ``Exists #[·]) mkAnd]
      | .all xs P => do
        makeBinder quant xs P mkForallFVars pure <| mkForall `_ .default
      | .exists xs P => do
        mkAppM ``Exists #[← makeBinder quant xs P mkLambdaFVars (mkAppM ``Exists #[·]) mkAnd]
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
              let P ← checkpoint "lam:dom" quant P.toExpr pure

              let y ← mkFreshBinderName
              let lam ← withLocalDeclD y β fun y ↦ do
                let F ← checkpoint "lam:val" quant (λ q hyps ↦ do
                  -- We need to checkpoint around ``
                  let F ← F.toExpr q hyps

                  assignMVar β (← inferType F)

                  liftMetaM <| mkEq y F) pure
                let β ← instantiateMVars β

                let xs' ← do
                  xs[1:].foldlM (init := ← lookupVar xs[0]!.fst) fun acc ⟨xᵢ, _⟩ ↦ do
                    mkAppM ``Prod.mk #[acc, ← lookupVar xᵢ]
                -- x̄ = (xs', y)
                let eq : Expr ← mkEq zvec (mkApp4 (mkConst ``Prod.mk [levelα, lmvar]) α β xs' y)
                -- y = F[x̄/xs']
                -- let eqF : Expr ← mkEq y F
                -- x̄ = (xs', y) ∧ P[x̄/xs'] ∧ y = F[x̄/xs']
                mkLambdaFVars #[y] <| mkAndN [eq, P, F]
              mkAppM ``Exists #[lam]
            | ⟨x, t⟩ :: xs => do
              let lam ← withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y =>
                (liftMetaM ∘ mkLambdaFVars #[y] =<< go xs)
              mkAppM ``Exists #[lam]

          liftMetaM ∘ mkLambdaFVars #[zvec] =<< go xs.toList
        mkAppM ``setOf #[lam]
      | .interval lo hi => makeBinary quant hyps ``Builtins.interval lo hi
      | .subset S T => makeBinary quant hyps ``HasSubset.Subset S T
      | .set es ty => do
        if es.isEmpty then
          mkAppOptM ``EmptyCollection.emptyCollection #[ty.toExpr, .none]
        else
          let emp ← mkAppOptM ``Singleton.singleton #[.none, ty.toExpr, .none, ← es.back!.toExpr quant hyps]
          es.pop.foldrM (init := emp) fun e acc ↦ do mkAppM ``Insert.insert #[←e.toExpr quant hyps, acc]
      | .setminus S T => makeBinary quant hyps ``SDiff.sdiff S T
      | .pow S => makeUnary quant hyps ``Set.powerset S
      | .pow₁ S => makeUnary quant hyps ``Builtins.POW₁ S
      | .cprod S T => makeBinary quant hyps ``SProd.sprod S T
      | .union S T => makeBinary quant hyps ``Union.union S T
      | .inter S T => makeBinary quant hyps ``Inter.inter S T
      | .rel A B => makeBinary quant hyps ``B.Builtins.rels A B
      | .image R X => makeBinary quant hyps ``SetRel.image R X
      | .inv R => makeUnary quant hyps ``SetRel.inv R
      | .id A => makeUnary quant hyps ``B.Builtins.id A
      | .dom f => makeUnary quant hyps ``B.Builtins.dom f
      | .ran f => makeUnary quant hyps ``B.Builtins.ran f
      | .domRestr R E => makeBinary quant hyps ``B.Builtins.domRestr E R
      | .domSubtr R E => makeBinary quant hyps ``B.Builtins.domSubtr E R
      | .codomRestr R E => makeBinary quant hyps ``B.Builtins.codomRestr R E
      | .codomSubtr R E => makeBinary quant hyps ``B.Builtins.codomSubtr R E
      | .fun A B isPartial =>
        makeBinary quant hyps (if isPartial then ``B.Builtins.pfun else ``B.Builtins.tfun) A B
      | .injfun A B isPartial => do
        makeBinary quant hyps (if isPartial then ``B.Builtins.injPFun else ``B.Builtins.injTFun) A B
      | .surjfun A B isPartial => do
        makeBinary quant hyps (if isPartial then ``B.Builtins.surjPFun else ``B.Builtins.surjTFun) A B
      | .bijfun A B isPartial => do
        makeBinary quant hyps (if isPartial then ``B.Builtins.bijPFun else ``B.Builtins.bijTFun) A B
      | .min S => do
        let S ← S.toExpr quant hyps
        let wf ← mkAppM ``B.Builtins.min.WF #[S]
        makeWFHypothesis hyps wf λ h ↦ mkAppM ``B.Builtins.min #[S, h]
      | .max S => do
        let S ← S.toExpr quant hyps
        let wf ← mkAppM ``B.Builtins.max.WF #[S]
        makeWFHypothesis hyps wf λ h ↦ mkAppM ``B.Builtins.max #[S, h]
      | .app f x => do
        let f ← f.toExpr quant hyps
        let x ← x.toExpr quant hyps
        let wf ← mkAppM ``B.Builtins.app.WF #[f, x]
        makeWFHypothesis hyps wf λ h ↦ mkAppM ``B.Builtins.app #[f, x, h]
      | .fin S => makeUnary quant hyps ``B.Builtins.FIN S
      | .fin₁ S => makeUnary quant hyps ``B.Builtins.FIN₁ S
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

      let g ← checkpoint "goal" .ex sg.goal.toExpr pure

      trace[barrel.pog] "Generated goal (no quantified variable): {indentExpr g}"

      let g ← liftMetaM (mkForallFVars vars (usedOnly := true) g)
              >>= Term.ensureHasType (.some <| .sort 0)
      Meta.check g
      let g ← instantiateMVars g
      Meta.liftMetaM g.ensureHasNoMVars
      return g

end B
