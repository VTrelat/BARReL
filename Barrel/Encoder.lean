import POGReader.Basic
import Barrel.Meta
import Barrel.Builtins
import Barrel.Subsume
import Barrel.WDReuse

open Std Lean Meta Elab Term

namespace B

  namespace Encoder

  /-- Ignore binder names and source metadata when comparing closed WD conditions. -/
  private partial def canonWD : Expr → Expr
    | .forallE _ t b bi => .forallE .anonymous (canonWD t) (canonWD b) bi
    | .lam _ t b bi => .lam .anonymous (canonWD t) (canonWD b) bi
    | .letE _ t v b nd => .letE .anonymous (canonWD t) (canonWD v) (canonWD b) nd
    | .app f a => .app (canonWD f) (canonWD a)
    | .mdata _ e => canonWD e
    | .proj n i e => .proj n i (canonWD e)
    | e => e

  /-- One closed proof metavariable, allocated only on a WD cache miss. -/
  structure WD where
    name : Name
    type : Expr
    proof : Expr
    order : Nat := 0
    deriving Inhabited

  /-- A condition discharged by a published fact, before allocating a local WD goal. -/
  structure Reuse extends WD where
    theoremName : Name
    value : Expr

  /-- Import-local encoder state; its metavariables belong to the enclosing `TermElabM`. -/
  structure State where
    config : Barrel.ImportConfig := {}
    earlier : Barrel.WDReuse.Index := {}
    wds : Array WD := #[]
    reused : Array Reuse := #[]
    seen : Std.HashMap Expr Expr := {}
    names : Std.HashMap MVarId Name := {}
    allocations : Nat := 0
    hits : Nat := 0
    defEqHits : Nat := 0
    subsumptionHits : Nat := 0
    nextWD : Nat := 0
    nextProof : Nat := 0

  abbrev M := StateT State TermElabM

  /-- Export named references without assigning the proof metavariables used by the encoder. -/
  def State.export (s : State) (e : Expr) : Expr :=
    e.replace fun e => do
      guard e.isMVar
      return mkConst (← s.names[e.mvarId!]?)

  /-- Prefer an earlier definitionally equal WD, then try subsumption under the same budget.
  The target and candidates are closed; source locals must not escape into cached adapters. -/
  def State.findProof? (s : State) (type : Expr) : MetaM (Option Barrel.Subsume.Match) := do
    let limit := s.config.subsumeMaxHeartbeats
    if limit == 0 then return none
    -- Keep encounter order across allocated and reused facts. Searching all local
    -- goals first can exhaust the cap before an earlier, smaller adapter is tried.
    let candidates := if s.reused.isEmpty then s.wds
      else (s.wds ++ s.reused.map (·.toWD)).qsort (·.order < ·.order)
    withOptions (barrel.subsume.maxHeartbeats.set · limit) <|
      withLCtx {} #[] <| Barrel.Subsume.match? type (candidates.map (·.proof))

  private def State.findEarlier? (s : State) (type : Expr) : MetaM (Option (Expr × Name)) :=
    withLCtx {} #[] <| Barrel.WDReuse.findProof? s.earlier type s.config.subsumeMaxHeartbeats

  /-- Local sharing and cross-import lookup spend one cumulative encoder search budget. -/
  private def State.search? (s : State) (type : Expr) : MetaM
      (Option (Barrel.Subsume.Match × Option Name)) := do
    let hasEarlier := barrel.reuse_wd.get (← getOptions) &&
      ((Barrel.WDReuse.head? type).bind s.earlier.find?).any (!·.isEmpty)
    -- Preserve the existing local-search budget exactly when there is no external bucket.
    if !hasEarlier then return (← s.findProof? type).map (·, none)
    Barrel.WDReuse.withBudget? s.config.subsumeMaxHeartbeats do
      if let some found ← s.findProof? type then return some (found, none)
      if let some (proof, name) ← s.findEarlier? type then
        return some ({ proof, kind := .subsumption }, some name)
      return none

  /-- Resolve provisional types and merge WDs whose reuse depended on later type inference. -/
  def State.refresh (s : State) (firstWD : Nat) : TermElabM State := do
    let fresh := s.wds[firstWD:].toArray
    let aliases := s.seen
    let mut s := { s with wds := s.wds.extract 0 firstWD, seen := {} }
    -- Discard provisional aliases as well as original keys. Rebuild in dependency order
    -- so no proof can be matched against itself.
    for wd in s.wds do
      s := { s with seen := s.seen.insert (canonWD wd.type) wd.proof }
    let firstOrder := (fresh[0]?.map (·.order)).getD s.nextProof
    for wd in s.reused.filter (·.order < firstOrder) do
      s := { s with seen := s.seen.insert (canonWD wd.type) wd.proof }
    for wd in fresh do
      for earlier in s.reused.filter (·.order < wd.order) do
        s := { s with seen := s.seen.insert (canonWD earlier.type) earlier.proof }
      let type ← instantiateMVars wd.type
      let key := canonWD type
      let found? ← match s.seen[key]? with
        | some proof => pure (some ({ proof, kind := .defEq }, none))
        | none => do
          if type == wd.type then pure none
          else ({ s with reused := s.reused.filter (·.order < wd.order) }).search? type
      if let some (found, earlier?) := found? then
        let proof := found.proof
        if let some theoremName := earlier? then
          s := { s with
            reused := s.reused.push { wd with type, theoremName, value := proof }
            seen := s.seen.insert key wd.proof }
        else
          wd.proof.mvarId!.assign proof
          s := { s with
            seen := s.seen.insert key proof
            names := s.names.erase wd.proof.mvarId! }
      else
        s := { s with
          wds := s.wds.push { wd with type }
          seen := s.seen.insert key wd.proof }
    -- Restore aliases only after merging, when they cannot make a fresh WD match itself.
    -- Instantiate both sides so references to a merged WD follow its earlier proof.
    for (type, proof) in aliases do
      let resolved ← instantiateMVars type
      let key := if resolved == type then type else canonWD resolved
      let proof ← instantiateMVars proof
      s := { s with seen := s.seen.insert key proof }
    return s

  /-- Close over the proof context before lookup, and apply the shared proof to that context. -/
  private def wellDefined (type : Expr) : M Expr := do
    let locals := (← getLCtx).getFVars
    let args ← locals.filterM fun x => return !(← x.fvarId!.isLetVar)
    let type ← instantiateMVars (← mkForallFVars locals type)
    let key := canonWD type
    let s ← get
    modify fun s => { s with nextWD := s.nextWD + 1 }
    if let some proof := s.seen[key]? then
      modify fun s => { s with hits := s.hits + 1 }
      return (mkAppN proof args).headBeta
    let name := (← getDeclName?).get!.str s!"wd_{s.nextWD}"
    if let some (found, earlier?) ← s.search? type then
      if let some theoremName := earlier? then
        trace[barrel.wd] "Reused WD {name} from earlier theorem {theoremName}"
        -- A checked theorem wrapper retains the original context and dependent
        -- introductions. It is already proved and never enters the obligation queue.
        let proof ← mkFreshExprMVarAt {} #[] type .syntheticOpaque
        modify fun s => { s with
          reused := s.reused.push {
            name, type, proof, order := s.nextProof, theoremName, value := found.proof }
          seen := s.seen.insert key proof
          names := s.names.insert proof.mvarId! name
          nextProof := s.nextProof + 1 }
        return mkAppN proof args
      else
        modify fun s => { s with
          seen := s.seen.insert key found.proof
          hits := s.hits + 1
          defEqHits := s.defEqHits + if found.kind == .defEq then 1 else 0
          subsumptionHits := s.subsumptionHits + if found.kind == .subsumption then 1 else 0 }
        return (mkAppN found.proof args).headBeta
    let proof ← mkFreshExprMVarAt {} #[] type .syntheticOpaque
    trace[barrel.wd] "New WD metavariable {name}: {indentExpr type}"
    modify fun s => { s with
      wds := s.wds.push { name, type, proof, order := s.nextProof }
      seen := s.seen.insert key proof
      names := s.names.insert proof.mvarId! name
      allocations := s.allocations + 1
      nextProof := s.nextProof + 1 }
    return mkAppN proof args

  end Encoder

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

  private def newMVar (type : Lean.Expr) : MetaM Expr := do
    -- B types do not depend on term variables. Keep the lambda result type outside
    -- their scope so closing a WD cannot raise it before result-type inference finishes.
    let mvar ← Meta.mkFreshExprMVarAt {} #[] type
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

  -- Integer literals remain Int; only cast them when a real operand or context requires it.
  private def coerceNumeric (e target : Expr) : MetaM Expr := do
    let source ← whnf (← inferType e)
    let target ← whnf target
    if source.isConstOf ``Int && target.isConstOf ``Real then
      return ← mkAppOptM ``Int.cast #[target, none, e]
    return e

  private def promoteNumeric (left right : Expr) : MetaM (Expr × Expr) := do
    let leftType ← whnf (← inferType left)
    let rightType ← whnf (← inferType right)
    if leftType.isConstOf ``Real && rightType.isConstOf ``Int then
      return (left, ← coerceNumeric right leftType)
    if leftType.isConstOf ``Int && rightType.isConstOf ``Real then
      return (← coerceNumeric left rightType, right)
    return (left, right)

  private def setElementType (S : Expr) : MetaM Expr := do
    let .forallE _ α _ _ ← whnf (← inferType S)
      | throwError "Expected a B set, got {S}"
    return α

  private def realLiteral (value : Rat) : MetaM Expr := do
    let numerator ← mkNumeral (mkConst ``Real) value.num.natAbs
    let numerator ← if value.num < 0 then mkAppM ``Neg.neg #[numerator] else pure numerator
    if value.den == 1 then return numerator
    mkAppM ``HDiv.hDiv #[numerator, ← mkNumeral (mkConst ``Real) value.den]

  mutual
    partial def makeBinary (f : Name) (t₁ t₂ : Syntax.Term) : Encoder.M Expr := do
      mkAppM f #[← t₁.toExpr, ← t₂.toExpr]

    partial def makeUnary (f : Name) (t : Syntax.Term) : Encoder.M Expr := do
      mkAppM f #[← t.toExpr]

    partial def makeNumericBinary (f : Name) (t₁ t₂ : Syntax.Term) : Encoder.M Expr := do
      let (x, y) ← promoteNumeric (← t₁.toExpr) (← t₂.toExpr)
      mkAppM f #[x, y]

    partial def Syntax.Term.toExpr : Syntax.Term → Encoder.M Expr
      | .var v => if v ∈ B.Syntax.reservedIdentifiers then reservedVarToExpr v else lookupVar v
      | .int n => return mkIntLit n
      | .real value => realLiteral value
      | .uminus x => makeUnary ``Neg.neg x
      | .le x y => makeNumericBinary ``LE.le x y
      | .lt x y => makeNumericBinary ``LT.lt x y
      | .bool b => return mkConst (if b then ``True else ``False)
      | .maplet x y => makeBinary ``Prod.mk x y
      | .add x y => makeNumericBinary ``HAdd.hAdd x y
      | .sub x y => makeNumericBinary ``HSub.hSub x y
      | .mul x y => makeNumericBinary ``HMul.hMul x y
      | .div x y => do
        let (x, y) ← promoteNumeric (← x.toExpr) (← y.toExpr)
        -- B's division is partial (`y ≠ 0`). On integers it truncates towards zero
        -- (`-7 / 2 = -3`), whereas `/` on `Int` is Euclidean in Lean (`-7 / 2 = -4`).
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.div.WD #[y])
        if (← whnf (← inferType x)).isConstOf ``Int then
          mkAppM ``B.Builtins.div #[x, y, wdMVar]
        else
          mkAppM ``B.Builtins.rdiv #[x, y, wdMVar]
      | .mod x y => do
        -- B's `mod` is partial: it is defined for `x ∈ NATURAL` and `y ∈ NATURAL1` only.
        let x ← x.toExpr
        let y ← y.toExpr
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.mod.WD #[x, y])
        mkAppM ``B.Builtins.mod #[x, y, wdMVar]
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
      | .eq x y => do
        let (x, y) ← promoteNumeric (← x.toExpr) (← y.toExpr)
        mkEq x y
      | .mem x S => do
        let S ← S.toExpr
        let x ← coerceNumeric (← x.toExpr) (← setElementType S)
        mkAppM ``Membership.mem #[S, x]
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
        let rec go_forall : List (String × Syntax.Typ) → Encoder.M Expr
          | [] => P.toExpr
          | ⟨x, t⟩ :: xs => do
            withLocalDeclD (Name.mkStr1 x) (t.toExpr) fun y ↦ do
              (liftMetaM ∘ mkForallFVars #[y] =<< go_forall xs)

        go_forall xs.toList
      | .exists xs P => do
        let rec go_exists : List (String × Syntax.Typ) → Encoder.M Expr
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
          let .pow elemTy := ty | throwError "Expected a set type, got {ty}"
          let elemTy := elemTy.toExpr
          let last ← coerceNumeric (← es.back!.toExpr) elemTy
          let emp ← mkAppOptM ``Singleton.singleton #[elemTy, ty.toExpr, .none, last]
          es.pop.foldrM (init := emp) fun e acc ↦ do
            mkAppM ``Insert.insert #[← coerceNumeric (← e.toExpr) elemTy, acc]
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
      | .domRestr E R => makeBinary ``B.Builtins.domRestr E R
      | .domSubtr E R => makeBinary ``B.Builtins.domSubtr E R
      | .codomRestr R E => makeBinary ``B.Builtins.codomRestr R E
      | .codomSubtr R E => makeBinary ``B.Builtins.codomSubtr R E
      | .overload R T => makeBinary ``B.Builtins.overload R T
      | .seq E => makeUnary ``B.Builtins.seq E
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
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.min.WD #[S])
        mkAppM ``B.Builtins.min #[S, wdMVar]
      | .max S => do
        let S ← S.toExpr
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.max.WD #[S])
        mkAppM ``B.Builtins.max #[S, wdMVar]
      | .app f x => do
        let f ← f.toExpr
        let pairType ← whnf (← setElementType f)
        unless pairType.isAppOfArity ``Prod 2 do throwError "Expected a B relation, got {f}"
        let x ← coerceNumeric (← x.toExpr) pairType.getAppArgs[0]!
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.app.WD #[f, x])
        mkAppM ``B.Builtins.app #[f, x, wdMVar]
      | .size E => do
        let E ← E.toExpr
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.size.WD #[E])
        mkAppM ``B.Builtins.size #[E, wdMVar]
      | .fin S => makeUnary ``B.Builtins.FIN S
      | .fin₁ S => makeUnary ``B.Builtins.FIN₁ S
      | .card S => do
        let S ← S.toExpr
        let wdMVar ← Encoder.wellDefined (← mkAppM ``B.Builtins.card.WD #[S])
        mkAppM ``B.Builtins.card #[S, wdMVar]

  end

  /-- Encode one goal, allocating only previously unseen WDs in the shared import session. -/
  def POG.Goal.toExpr (sg : POG.Goal) (declName : Name) (state : Encoder.State) :
      TermElabM (Expr × Array (Name × Expr) × Encoder.State) := withDeclName declName do
    let firstWD := state.wds.size
    let (g, state) ← (do
      let vars : Array (Name × (Array Expr → Encoder.M Expr)) :=
        sg.vars.map λ ⟨x, τ⟩ ↦ ⟨.mkStr1 x, λ _ ↦ pure τ.toExpr⟩
      withLocalDeclsD vars fun vars => do
        trace[barrel] "Decoded goal: {sg.goal}"
        let g ← sg.goal.toExpr
        let g ← mkForallFVars vars g (usedOnly := true)
        let g ← Term.ensureHasType (some <| .sort 0) g
        Meta.check g
        instantiateMVars g : Encoder.M Expr).run { state with nextWD := 0 }
    let state ← state.refresh firstWD
    let wds ← state.wds[firstWD:].toArray.mapM fun wd => do
      let type := state.export (← instantiateMVars wd.type)
      if type.hasMVar || type.hasFVar then
        throwError "Unresolved variables in WD obligation `{wd.name}`"
      pure (wd.name, type)
    let g := state.export (← instantiateMVars g)
    if g.hasMVar || g.hasFVar then
      throwError "Unresolved variables in proof obligation `{declName}`"
    trace[barrel] "Generated theorem: {g}"
    return (g, wds, state)

end B
