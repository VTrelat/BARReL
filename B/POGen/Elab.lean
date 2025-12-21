import B.DSL.Machine
import B.AST
import B.POGen.Env
import Barrel.Builtins

def Array.partitionMap {α β γ} (f : α → β ⊕ γ) (a : Array α) : Array β × Array γ :=
  let rec go (i : ℕ) (acc₁ : Array β) (acc₂ : Array γ) : Array β × Array γ :=
    if _h : i < a.size then match f a[i] with
      | .inl x => go (i + 1) (acc₁.push x) acc₂
      | .inr x => go (i + 1) acc₁ (acc₂.push x)
    else
      (acc₁, acc₂)
  go 0 #[] #[]

namespace Lean.Elab.Term
  def elabTermEnsuringTypeAndSynthesize (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone := true) (implicitLambda := true) (errorMsgHeader? : Option String := none) : TermElabM Expr := do
    let e ← elabTerm stx expectedType? catchExPostpone implicitLambda
    try
      withRef stx <| instantiateMVars (← withSynthesize <| ensureHasType expectedType? e errorMsgHeader?)
    catch ex =>
      if (← read).errToSorry && ex matches .error .. then
        withRef stx <| exceptionToSorry ex expectedType?
      else
        throw ex
end Lean.Elab.Term

namespace B
  open Lean

  def set_decl.extractSets : TSyntax ``set_decl → Ident × Array Ident
    | `(set_decl| $x:ident) => (x, #[])
    | `(set_decl| $x:ident := {$xs:ident,*}) => (x, xs.getElems)
    | _ => unreachable!

  def constant_decl.extractConst : TSyntax ``constant_decl → Binding Ident Term
    | `(constant_decl| $x ∈ $t) => ⟨x, .in, t⟩
    | `(constant_decl| $x := $t) => ⟨x, .eq, t⟩
    | _ => unreachable!

  def var_decl.extractVar : TSyntax ``var_decl → Binding Ident Term
    | `(var_decl| $x ∈ $t) => ⟨x, .in, t⟩
    | _ => unreachable!

  def prop_decl.extract : TSyntax ``prop_decl → Ident × Term
    | `(prop_decl| $h : $t) => (h, t)
    | _ => unreachable!

  open Elab Command

  mutual
    partial def elabSubstitution_op : TSyntax `substitution_op → Substitution Ident Term .level1
      | `(substitution_op| begin $s end) => .block (elabSubstitution s).2
      | `(substitution_op| skip) => .identity
      | `(substitution_op| $xs:ident,* := $es:term,*) => .become_equal₁ xs es
      | `(substitution_op| pre $b:prop_decl* then $s end) => panic! "TODO (pre)"
      | `(substitution_op| assert $b:prop_decl* then $s end) => panic! "TODO (assert)"
      | `(substitution_op| $xs:ident,* :∈ $e) => panic! "TODO (:∈)"
      | `(substitution_op| $xs:ident,* :( $e )) => panic! "TODO (:())"
      | `(substitution_op| any $vs:var_decl* $[where $b:prop_decl*]? then $s end) =>
        .any (vs.map var_decl.extractVar) (b.getD #[] |>.map prop_decl.extract) (elabSubstitution s).2
      | _ => unreachable!

    partial def elabSubstitution : TSyntax `substitution → Σ k, Substitution Ident Term k
      | `(substitution| $s:substitution_op) => ⟨_, elabSubstitution_op s⟩
      | `(substitution| $s₁ ; $s₂) => ⟨_, .seq (elabSubstitution s₁).2 (elabSubstitution s₂).2⟩
      | `(substitution| $s₁ ‖ $s₂) => ⟨_, .par (elabSubstitution s₁).2 (elabSubstitution s₂).2⟩
      | _ => unreachable!
  end

  def elabOperation : TSyntax ``operation → MacroM (Operation Ident Term)
    | `(operation| $header:op_header $[($params:var_decl,*)]? := $sub:substitution_op) => do
      let (bound, name) := match header with
        | `(op_header| $x:ident $[$[, $xs:ident]* ← $y:ident]?) =>
          if let .some y := y then (#[x] ++ xs.getD #[], y) else (#[], x)
        | _ => unreachable!
      let params := params.getD ⟨#[]⟩ |>.getElems.map var_decl.extractVar
      return {
        bound
        name
        params
        subst := elabSubstitution_op sub
      }
    | stx => panic! s!"Unsupported operation syntax {stx}"

  ------------

  private def lookupVar (x : Name) : TermElabM Expr := do
    let some e := (← getLCtx).findFromUserName? x
      | throwError "No variable {x} found in context"
    return e.toExpr

  /--
    Generates the name of the inner `.enum` inductive of an abstract enumerated set `S` in machine named `m`.
  -/
  macro "enum_name% " S:term : term => `(Name.str $S "enum")
  macro "enum_ctor_name% " c:term " of " S:term : term => `((enum_name% $S) ++ $c)
  macro "enum_name% " S:term " in " m:term : term => `($m ++ enum_name% $S)
  macro "enum_ctor_name% " c:term " of " S:term " in " m:term : term => `((enum_name% $S in $m) ++ $c)
  macro "constants_name% " m:term : term => `(Name.str $m "Consts")
  macro "invariants_name% " m:term : term => `(Name.str $m "Invariants")
  macro "assertions_name% " m:term : term => `(Name.str $m "Assertions")

  macro S:term "_abs%" : term => `(Name.appendAfter $S "_abs")
  macro S:term "_def%" : term => `(Name.appendAfter $S "_def")
  macro S:term "_type%" : term => `(Name.appendAfter $S "_type")

  -- /-
  --   * `(begin σ end)·t ≡ σ·t`
  --   * `skip·t ≡ t`
  --   * `(x₁, .., xₙ ≔ e₁, …, eₙ)·t ≡ [xᵢ ↦ eᵢ]·t`
  --   * `(x(e₁, …, eₙ) := e)·t ≡ ?`
  --   * `(pre p then σ)·t ≡ p ⇒ σ·t`
  --   * `(assert p then σ)·t ≡ p ∧' σ·t`
  --   * `(choice σ₁ or … or σₙ)·t ≡ σ₁·t ∧ … ∧ σₙ·t`
  --   * `(if p₁ then σ₁ elsif … else σ)·t ≡ (p₁ ⇒ σ₁·t) ∧ (¬p₁ ⇒ p₂ ⇒ σ₂·t) ∧ … ∧ (⋀(¬pᵢ) ⇒ σ·t)`
  --   * `(select p₁ then σ₁ when p₂ then σ₂ … else σ)·t ≡ (p₁ ⇒ σ₁·t) ∧ (p₂ ⇒ σ₂·t) ∧ … ∧ (⋀(¬pᵢ) ⇒ σ·t)`
  --   * `(any x where p then σ)·t ≡ ∀ x, p ⇒ σ·t`
  --   * `(let x be x ≔ e in σ)·t ≡ ∀ x, x = e ⇒ σ·t`
  --   * `(x₁, …, xₙ :∈ e)·t` ≡ ∀ x₁ ∈ e, …, xₙ ∈ e, t`
  --   * `(x₁, …, xₙ :( p ))·t ≡ ∀ x₁, …, xₙ, p ⇒ t`
  --   * `(var v₁, …, vₙ then σ)·t ≡ ∀ v₁, …, vₙ, σ·t`
  --   * `(σ₁; σ₂)·t ≡ σ₁·(σ₂·t)`
  --   * `(σ₁ ‖ σ₂)·t ≡ ?`
  -- -/
  -- private def Substitution.apply (t : Expr) : {k : _} → Substitution Expr Expr k → TermElabM Expr
  --   | .level1, .block s => s.apply t
  --   | .level1, .identity => return t
  --     -- FIXME: the FVars do not exist in the local context anymore!
  --   | .level1, .become_equal₁ vs es => return t.replaceFVars vs es
  --   | .level1, .become_equal₂ v es e => panic! "TODO"
  --     -- FIXME: the FVars do not exist in the local context anymore!
  --   | .level1, .precond p s => do Meta.mkForallFVars (p.map Prod.fst) (← s.apply t)
  --     -- FIXME: the FVars do not exist in the local context anymore!
  --   | .level1, .assert p s =>
  --     let f := p.foldr (init := λ _ ↦ s.apply t) λ (h, p) concl ↦ λ _ ↦ do
  --       let concl ← Meta.liftMetaM <| Meta.mkLambdaFVars #[h] (← concl ())
  --       Meta.mkAppM ``DepAnd #[p, concl]
  --     f ()
  --   | .level1, .choice ss => panic! "TODO"
  --   | .level1, .if ss₁ s₂ => panic! "TODO"
  --   | .level1, .select ss₁ s₂ => panic! "TODO"
  --   | .level1, .any vs ps s => do
  --     -- FIXME: the FVars do not exist in the local context anymore!
  --     Meta.mkForallFVars (vs.map Binding.name ++ ps.map Prod.fst) (← s.apply t)
  --   | .level1, .let vs eqs s => panic! "TODO"
  --   | .level1, .become_element vs e => panic! "TODO"
  --   | .level1, .become_such_that vs p => panic! "TODO"
  --   | .level1, .var vs s => panic! "TODO"
  --   | .any, .seq s₁ s₂ => s₁.apply =<< s₂.apply t
  --   | .any, .par s₁ s₂ => panic! "TODO"

  -- def generateProofObligations (m : Machine Binder Expr) :
  --     TermElabM (Array (Name × String × Expr)) := do
  --   let mut pos := #[]

  --   if !m.includes.isEmpty then
  --     throwError "TODO: handle machine inclusion"

  --   if !m.assertions.isEmpty then
  --     let assName := (← getCurrNamespace).str "ass"
  --     (pos, _, _) ← m.assertions.foldlM (init := (pos, #[], 1)) λ (pos, acc, k) (v, t) ↦ do
  --       --   Aₘ /- ∧ Aᵤ -/                                       -- Parameter constraints
  --       -- ∧ Bₘ /- ∧ Bᵤ ∧ Bₛ ∧ Bᵢ₍₁₎ ∧ … ∧ Bᵢ₍ₙ₎ -/              -- Properties
  --       -- /- ∧ Iᵤ ∧ Jᵤ -/
  --       -- ∧ Iₘ ∧ Lₘ                                             -- Invariants
  --       -- ∧ Jₘ₍₁₎ ∧ … ∧ Jₘ₍ₖ₋₁₎                                 -- Previous assertions
  --       -- ──────────────────────────────────────────────────────────────────────────────────
  --       -- ⊢ Jₘ₍ₖ₎
  --       let fvars := Array.flatten #[
  --         ← m.props,
  --         ← m.invs,
  --         acc
  --       ]
  --       let goal ← withBinders fvars λ oldFVars newFVars ↦ Meta.mkForallFVars newFVars (t.replaceFVars oldFVars newFVars)
  --       return (
  --         pos.push (
  --           assName.appendAfter k.toSubscriptString,
  --           s!"Assertion `{(← v.fvar.fvarId!.getUserName).toString true}` of machine `{m.name}` is satisfied",
  --           goal
  --         ),
  --         acc.push v,
  --         k + 1
  --       )

  --   if !m.invariants.isEmpty || !m.abstract_variables.isEmpty || !m.concrete_variables.isEmpty then
  --     let init_sub := m.initialisation.2

  --     --   Aₘ /- ∧ Aᵤ -/
  --     -- ∧ Bₘ /- ∧ Bᵤ ∧ Bₛ ∧ Bᵢ₍₁₎ ∧ … ∧ Bᵢ₍ₙ₎ -/
  --     -- /- ∧ Iᵤ ∧ Jᵤ -/
  --     -- /- ∧ Iₛ ∧ Jₛ -/
  --     -- ──────────────────────────────────────────────────────────────────────────────────
  --     -- ⊢ Uₘ • Iₘ
  --     let fvars := Array.flatten #[
  --       ← m.props
  --     ]
  --     let invName := (← getCurrNamespace).str "init" |>.str "inv"
  --     (pos, _) ← ((m.abstract_variables ++ m.concrete_variables).map λ b ↦ (b.name, b.type)) ++ m.invariants
  --       |>.foldlM (init := (pos, 1)) λ (pos, k) (h, inv) ↦ do
  --         if ← Meta.isProp (← h.fvarId!.getType) then
  --           return (
  --             pos.push (
  --               invName.appendAfter k.toSubscriptString,
  --               s!"Invariant `{(← h.fvarId!.getUserName).toString true}` is preserved by initialisation",
  --               ← Meta.mkForallFVars fvars <| ← init_sub.apply inv
  --             ),
  --             k + 1
  --           )
  --         else
  --           return (pos, k)


  --     -- panic! "TODO: generate invariant preservation (init & ops)"

  --   return pos


  /-! # What a machine generates

  Given a B machine of the form
  ```lean
  machine A
  sets S₁, …, Sₖ
  constants c₁ ∈ Ac₁, …, cₘ ∈ Acₘ
  properties hp₁ : Pp₁, …, hpᵢ : Ppᵢ
  variables x₁ ∈ Av₁, …, xₙ ∈ Avₙ
  invariants hi₁ : Pi₁, …, hiⱼ : Piⱼ
  assertions ha₁ : Pa₁, …, haᵥ : Paᵥ
  initialisation Sinit
  operations op₁ := S₁, …, opₒ : Sₒ
  ```
  we generate a few constructs:

  * For every enumerated abstract set, an inductive type which contains all the elements of the set.
  * A structure named `A` containing all sets, constants, properties (including the typing of constants)
    and variables (without their typing).
  * A definition `A.invariant` (with parameter `mach : A`) containing a dependent conjunction of the typing of all
    variables as well as all the invariants.
  * A definition `A.assertion` (with parameters `mach : A` and `inv : mach.invariant`) containing a dependent
    conjunction of all assertions.
  -/

  -- This is bad, but I don't want to duplicate all this code!
  open private mkAuxConstructions from Lean.Elab.MutualInductive

  /--
    Generates the inductive types for the items of all abstract enumerated sets.
  -/
  private def generateAbstractEnumeratedSets (m : Machine Ident Term) : CommandElabM PUnit := do
    for (name, items) in m.sets do if !items.isEmpty then
      let ns ← getCurrNamespace
      let S_enum := ns ++ enum_name% name.getId in m.name.getId
      let itemsDecl : Declaration := .inductDecl [] 0 [{
        name := S_enum
        type := mkSort 1
        ctors := items.foldl (init := []) λ ctors ctorName ↦
          ctors.concat { name := ns ++ enum_ctor_name% ctorName.getId of name.getId in m.name.getId, type := .const S_enum [] }
      }] false
      liftTermElabM do
        addDecl itemsDecl
        mkAuxConstructions #[S_enum]

  def withLocalSets {α} (m_name : Ident) («sets» : Array (Ident × Array Ident)) (k : Array Expr → TermElabM α) : TermElabM α := do
    let rec go (i : ℕ) (acc : Array Expr) : TermElabM α := do
      if _h : i < «sets».size then
        let (S, items) := «sets»[i]

        -- For each set `S`:
        -- * If it is an abstract set: make a new type variable `α` and add `S : Set α` to the local declarations
        -- * If it is an enumerated set: create a new enumeration `S.items` and add `S : Set S.items` to the local declarations
        if items.isEmpty then
          let α ← mkFreshUserName `α

          Meta.withLocalDecl α .implicit (mkSort 1) λ α ↦ do
            Meta.withLocalDecl S.getId .default (mkApp (.const ``Set [0]) α) λ S' ↦ do
              let h ← Meta.mkAppM ``Membership.mem #[
                ← Meta.mkAppM ``Builtins.POW₁ #[
                  ← Meta.mkAppOptM ``Set.univ #[α]
                ],
                S'
              ]
              Meta.withLocalDecl (S.getId _abs%) .default h λ h ↦ do
                go (i + 1) (acc.push α |>.push S' |>.push h)
        else
          let S.items := (← getCurrNamespace) ++ enum_name% S.getId in m_name.getId
          Meta.withLocalDecl S.getId .default (mkApp (.const ``Set [0]) (.const S.items [])) λ S' ↦ do
            let h ← Meta.mkEq S' (← Meta.mkAppOptM ``Set.univ #[.some (.const S.items [])])
            Meta.withLocalDecl (S.getId _def%) .default h λ h ↦ do
              go (i + 1) (acc.push S' |>.push h)
      else
        k acc

    go 0 #[]

  def withBindings {α} (bindings : Array (Binding Ident Term)) (k : Array Expr → TermElabM α) : TermElabM α := do
    let rec go (i : ℕ) (acc : Array Expr) : TermElabM α := do
      if _h : i < bindings.size then
        let ⟨name, kind, t⟩ := bindings[i]

        match kind with
        | .in => do
          let α ← Meta.mkFreshTypeMVar
          let lmvar ← Meta.getDecLevel α
          let ty₁ ← Term.elabTermEnsuringTypeAndSynthesize t (Expr.app (.const ``Set [lmvar]) α)
          Term.synthesizeSyntheticMVarsNoPostponing
          let α ← instantiateMVars α

          Meta.withLocalDecl name.getId .default α λ name' ↦ do
            let ty₂ ← Meta.mkAppM ``Membership.mem #[ty₁, name']
            Meta.withLocalDecl (name.getId _type%) .default ty₂ λ h ↦ do
              go (i + 1) (acc.push name' |>.push h)
        | .eq => do
          let ty₁ ← Term.elabTermEnsuringTypeAndSynthesize t .none
          Term.synthesizeSyntheticMVarsNoPostponing
          let α ← Meta.inferType ty₁

          Meta.withLocalDecl name.getId .default α λ name' ↦ do
            let ty₂ ← Meta.mkEq name' ty₁
            Meta.withLocalDecl (name.getId _def%) .default ty₂ λ h ↦ do
              go (i + 1) (acc.push name' |>.push h)
      else
        k acc

    go 0 #[]

  def withVariableBindings {α} (bindings : Array (Binding Ident Term)) (k : Array (Expr ⊕ Expr) → TermElabM α) : TermElabM α := do
    let rec go (i : ℕ) (acc : Array (Expr ⊕ Expr)) : TermElabM α := do
      if _h : i < bindings.size then
        let ⟨name, kind, t⟩ := bindings[i]

        match kind with
        | .in => do
          let α ← Meta.mkFreshTypeMVar
          let lmvar ← Meta.getDecLevel α
          let ty₁ ← Term.elabTermEnsuringTypeAndSynthesize t (Expr.app (.const ``Set [lmvar]) α)
          Term.synthesizeSyntheticMVarsNoPostponing
          let α ← instantiateMVars α

          Meta.withLocalDecl name.getId .default α λ name' ↦ do
            let ty₂ ← Meta.mkAppM ``Membership.mem #[ty₁, name']
            Meta.withLocalDecl (name.getId _type%) .default ty₂ λ h ↦ do
              go (i + 1) (acc.push (.inl name') |>.push (.inr h))
        | .eq => do
          let ty₁ ← Term.elabTermEnsuringTypeAndSynthesize t .none
          Term.synthesizeSyntheticMVarsNoPostponing
          let α ← Meta.inferType ty₁

          Meta.withLocalDecl name.getId .default α λ name' ↦ do
            let ty₂ ← Meta.mkEq name' ty₁
            Meta.withLocalDecl (name.getId _def%) .default ty₂ λ h ↦ do
              go (i + 1) (acc.push (.inl name') |>.push (.inr h))
      else
        k acc

    go 0 #[]

  def withProps {α} (props : Array (Ident × Term)) (k : Array Expr → TermElabM α) : TermElabM α := do
    let rec go (i : ℕ) (acc : Array Expr) : TermElabM α := do
      if _h : i < props.size then
        let ⟨name, p⟩ := props[i]
        let p ← Term.elabTermEnsuringTypeAndSynthesize p (mkSort 0)
        Term.synthesizeSyntheticMVarsNoPostponing
        Meta.withLocalDecl name.getId .default p λ h ↦ do
          go (i + 1) (acc.push h)
      else
        k acc

    go 0 #[]

  -- This is ugly, but let's reuse what Lean already has, even if it is private...
  open private defaultCtorName mkToParentName from Lean.Elab.Structure in
  private def generateStructure (structName : Name) (vars : Array Expr) (type : Expr) (fields : Array Expr) (parents : Array Expr := #[]) : TermElabM PUnit := do
    let structType ← Meta.mkForallFVars vars type

    let lctx := vars.foldl (init := ← getLCtx) λ lctx v ↦ LocalContext.setBinderInfo lctx v.fvarId! .implicit
    Meta.withLCtx' lctx do
      let fields' := parents ++ fields

      let mk := structName ++ defaultCtorName
      let type' ← do
        let e₁ ← Meta.mkForallFVars fields (mkAppN (.const structName []) vars)
        let e₂ ← Meta.mkForallFVars parents e₁
        Meta.mkForallFVars vars e₂

      -- Generate the underlying inductive type
      -- logInfo m!"Generating constructor {mk} with type{indentExpr type'}"
      -- logInfo m!"Free vars of {mk}: {← (Array.map Expr.fvar ∘ CollectFVars.State.fvarIds ∘ Prod.snd) <$> Meta.liftMetaM (type'.collectFVars.run {})}"
      addDecl <| .inductDecl [] vars.size [{
        name := structName
        type := structType
        ctors := [{
          name := mk
          type := type'
        }]
      }] false
      withOptions (warn.sorry.set · false) do
        mkAuxConstructions #[structName]

      let fields'' : Array StructureFieldInfo ← fields'.mapM λ field ↦ do return {
        fieldName := ← field.fvarId!.getUserName
        projFn := structName ++ (← field.fvarId!.getUserName)
        subobject? := .none
        binderInfo := ← field.fvarId!.getBinderInfo
      }
      let parentFields : Array StructureFieldInfo ← parents.mapM λ name ↦ do return {
        fieldName := ← name.fvarId!.getUserName
        projFn := structName ++ (← name.fvarId!.getUserName)
        subobject? := .none
        binderInfo := .default
      }

      -- Then register our structure in the environment
      modifyEnv (registerStructure · { structName, fields := fields'' })
      setStructureParents structName =<< (parents.zip parentFields).mapM λ ⟨parent, f⟩ ↦ do
        return { f with
          structName := (← parent.fvarId!.getType).getAppFn.constName
          subobject := false
        }

      -- Generate the basic projections from the direct fields, including to the direct parents
      let projs : Array Meta.StructProjDecl ← fields'.mapM λ field ↦ do
        return { ref := Syntax.missing, projName := structName ++ (← field.fvarId!.getUserName) }
      -- logInfo m!"Generating projections {projs.map Meta.StructProjDecl.projName}"
      withOptions (warn.sorry.set · false) do
        Meta.mkProjections structName projs false
        for proj in projs do
          enableRealizationsForConst proj.projName

      let env ← getEnv
      let allParents := Lean.getStructureParentInfo env structName

      -- Then create the projections to the parents' fields
      let parentFields := allParents.map λ info ↦
        (info.structName, info.projFn, Lean.getStructureFieldsFlattened env info.structName (includeSubobjectFields := false))
      let projFns := parentFields.flatMap λ (name, proj, fields) ↦
        fields.filterMap λ f ↦ do
          let fieldProj ← Lean.getProjFnForField? env name f
          let projFn ← env.find? proj
          let fieldProjFn ← env.find? fieldProj
          return (projFn, f, fieldProjFn)
      withOptions (warn.sorry.set · false) do
        projFns.forM λ (projFn, field, fieldProjFn) ↦ do
          -- logInfo m!"Generating parent projection {field}"

          let e ← Meta.withLocalDeclD (← Term.mkFreshBinderName) (mkAppN (.const structName []) vars) λ x ↦ do
            let e ← Meta.mkAppM fieldProjFn.name #[← Meta.mkAppM projFn.name #[x]]
            Meta.mkLambdaFVars #[x] e
          let e ← Meta.mkLambdaFVars vars e
          let t ← Meta.inferType e
          addAndCompile <| .defnDecl {
            name := structName ++ field
            levelParams := []
            type := t
            value := e
            hints := .abbrev
            safety := .safe
          }

      -- Then create the flat constructor
      let allFlatCtors := allParents.map λ info ↦
        Lean.getStructureCtor env info.structName |>.name |> Lean.mkFlatCtorOfStructCtorName
      let allArgs := allFlatCtors.map λ ctor ↦ env.find? ctor |>.get!.type

      let rec constructFlatCtor (i : ℕ) : TermElabM (Expr × Expr) := do
        if _h : i < allArgs.size then
          Meta.forallTelescope allArgs[i] λ vs _ ↦ do
            let (type, body) ← constructFlatCtor (i + 1)

            return (
              ← Meta.mkForallFVars vs type,
              ← Meta.lambdaTelescope body λ vs' body ↦
                Meta.mkLambdaFVars (vs ++ vs') (.app body (mkAppN (.const allFlatCtors[i]! []) vs))
            )
        else
          return (
            ← Meta.mkForallFVars fields (mkAppN (.const structName []) vars),
            mkAppN (.const mk []) vars
          )

      let (type'', body'') ← constructFlatCtor 0
      let type'' ← Meta.mkForallFVars vars type''
      let body'' ← Meta.lambdaTelescope body'' λ vs body ↦
        Meta.mkLambdaFVars (vars ++ vs ++ fields) (mkAppN body fields)

        -- logInfo m!"Flat constructor:{indentExpr type''}{indentExpr body''}"

      withOptions (warn.sorry.set · false) do
        let info := env.find? mk |>.get!
        addAndCompile <| .defnDecl {
          name := Lean.mkFlatCtorOfStructCtorName mk
          levelParams := info.levelParams
          type := type''
          value := body''
          hints := info.hints
          safety := .safe
        }

  private def generateMachineStructure {α} (m : Machine Ident Term) (k : Array Expr → Array Expr → Array Expr → TermElabM α) : CommandElabM α := do
    liftTermElabM <| withLocalSets m.name m.sets λ sets ↦ do
      withBindings m.abstract_constants λ abstract_constants ↦ do
      withBindings m.concrete_constants λ concrete_constants ↦ do
        withProps m.properties λ properties ↦ do
          let fvars := sets ++ abstract_constants ++ concrete_constants ++ properties

          withVariableBindings m.abstract_variables λ abstract_variables ↦ do
          withVariableBindings m.concrete_variables λ concrete_variables ↦ do
            let (fvars', fvars'_typ) := (abstract_variables ++ concrete_variables).partitionMap id

            k fvars fvars' fvars'_typ

  private def makeProps {α} (fields : ExprMap Expr) (props : Array Expr) (k : ExprMap Expr → TermElabM α) : TermElabM α := do
    /- NOTE: accumulators

      The accumulators are present because we need to substitute free variables that have been introduced earlier
      with projections from the structure that we also created in an earlier scope (accessible via the `mach` free variable).

      This is quite ugly, and the scopes could/should be clearly defined at the cost of introducing more free variables.
    -/
    let rec go_prop (i : ℕ) (acc : ExprMap Expr) : TermElabM α := do
      if _h : i < props.size then
        let var := props[i]

        let defName ← var.fvarId!.getUserName
        let prop ← instantiateMVars =<< var.fvarId!.getType
        let prop' := prop.replace λ e ↦ acc[e]? <|> fields[e]?
        -- logInfo m!"makeProps:\n• prop (before) ={indentExpr prop}\n• prop' (after) ={indentExpr prop'}\n• to replace =\n  {fields ++ acc₁}\n• replaced by =\n  {toReplace ++ acc₂}\n• raw prop (before):\n  {repr prop}\n• raw prop' (after):\n  {repr prop'}"

        Meta.withLocalDecl defName .default prop' λ defName' ↦ do
          go_prop (i + 1) (acc.insert var defName')
      else
        k acc

    go_prop 0 .emptyWithCapacity

  private def generateInvariantStructure {α} (m : Machine Ident Term) (fields : Array Expr) (vars_typ : Array Expr) (mach : Expr) (invariants : Array Expr) (k : ExprMap Expr → TermElabM α) : TermElabM α := do
    -- TODO: converting the array to a list then constructing a map?
    let fields : ExprMap Expr ← (Std.HashMap.ofList ∘ Array.toList) <$> fields.mapM λ f ↦ do
      return (f, .app (.const ((← getCurrNamespace) ++ m.name.getId ++ (← f.fvarId!.getUserName)) []) mach)

    makeProps fields vars_typ λ vars_typ ↦ do
      makeProps (fields ∪ vars_typ) invariants λ invariants ↦ do
        k invariants

  private def generateAssertionStructure {α} (m : Machine Ident Term) (fields : Array Expr) (invariants : Array Expr) (mach machInv : Expr) (assertions : Array Expr) (k : ExprMap Expr → TermElabM α) : TermElabM α := do
    -- TODO: converting the array to a list then constructing a map?
    let fields : ExprMap Expr ← (Std.HashMap.ofList ∘ Array.toList) <$> fields.mapM λ f ↦ do
      return (f, .app (.const ((← getCurrNamespace) ++ m.name.getId ++ (← f.fvarId!.getUserName)) []) mach)
    let invariants : ExprMap Expr ← (Std.HashMap.ofList ∘ Array.toList) <$> invariants.mapM λ f ↦ do
      return (f, .app (.const ((← getCurrNamespace) ++ (invariants_name% m.name.getId) ++ (← f.fvarId!.getUserName)) []) machInv)

    makeProps (fields ∪ invariants) assertions λ assertions ↦ do
      k assertions

  partial def Substitution.variablesSet {α β} [BEq α] [Hashable α] : {k : _} → Substitution α β k → Std.HashSet α
    | .any, .seq s₁ s₂ => s₁.variablesSet ∪ s₂.variablesSet
    | .any, .par s₁ s₂ => s₁.variablesSet ∪ s₂.variablesSet
    | .level1, .block s => s.variablesSet
    | .level1, .identity => ∅
    | .level1, .become_equal₁ vs _ => Std.HashSet.ofArray vs
    | .level1, .become_equal₂ v _ _ => {v}
    | .level1, .precond _ s => s.variablesSet
    | .level1, .assert _ s => s.variablesSet
    | .level1, .choice ss => ss.foldl (init := ∅) λ acc s ↦ acc ∪ s.2.variablesSet
    | .level1, .if ss s => (ss.foldl (init := ∅) λ acc s ↦ acc ∪ s.2.2.variablesSet) ∪ match s with
      | .none => ∅
      | .some s => s.2.variablesSet
    | .level1, .select ss s => (ss.foldl (init := ∅) λ acc s ↦ acc ∪ s.2.2.variablesSet) ∪ match s with
      | .none => ∅
      | .some s => s.2.variablesSet
    | .level1, .any bs _ s => bs.foldl (init := s.variablesSet) λ s b => s.erase b.name
    | .level1, .let vs _ s => vs.foldl (init := s.variablesSet) Std.HashSet.erase
    | .level1, .become_element vs _ => Std.HashSet.ofArray vs
    | .level1, .become_such_that vs _ => Std.HashSet.ofArray vs
    | .level1, .var bs s => bs.foldl (init := s.variablesSet) λ s b => s.erase b.name

  -- private def checkSubstitution (m : Machine Ident Term) : {k : _} → Substitution Ident Term k → TermElabM (Σ k, Substitution Expr Expr k)
  --   | .level1, .block s => checkSubstitution m s
  --   | .level1, .identity => return ⟨_, .identity⟩
  --   | .level1, .become_equal₁ vs es => do
  --     -- let t ← Meta.ensureHasType t (.const ((← getCurrNamespace) ++ m.name.getId) [])
  --     let env ← getEnv
  --     let projs ← vs.mapM λ v ↦ do match env.find? ((← getCurrNamespace) ++ m.name.getId ++ v.getId) with
  --       | .none => unreachable!
  --       | .some e => return e
  --     panic! "TODO"
  --   | .level1, .become_equal₂ v es e => panic! "TODO"
  --   | .level1, .precond p s => panic! "TODO"
  --   | .level1, .assert p s => panic! "TODO"
  --   | .level1, .choice ss => panic! "TODO"
  --   | .level1, .if ss₁ s₂ => panic! "TODO"
  --   | .level1, .select ss₁ s₂ => panic! "TODO"
  --   | .level1, .any vs ps s => panic! "TODO"
  --   | .level1, .let vs eqs s => panic! "TODO"
  --   | .level1, .become_element vs e => panic! "TODO"
  --   | .level1, .become_such_that vs p => panic! "TODO"
  --   | .level1, .var vs s => panic! "TODO"
  --   | .any, .seq s₁ s₂ => panic! "TODO"
  --   | .any, @Substitution.par _ _ k₁ k₂ s₁ s₃ => panic! "TODO"

  private def Machine.structName {m : Type → Type} [Monad m] [MonadResolveName m] (mach : Machine Ident Term) : m Name := do
    return (← getCurrNamespace) ++ mach.name.getId

  private def Machine.structConstsName {m : Type → Type} [Monad m] [MonadResolveName m] (mach : Machine Ident Term) : m Name := do
    return constants_name% (← mach.structName)

  private def Machine.structInvariantsName {m : Type → Type} [Monad m] [MonadResolveName m] (mach : Machine Ident Term) : m Name := do
    return invariants_name% (← mach.structName)

  private def Machine.structAssertsName {m : Type → Type} [Monad m] [MonadResolveName m] (mach : Machine Ident Term) : m Name := do
    return assertions_name% (← mach.structName)

  open private mkToParentName from Lean.Elab.Structure

  private def elabMachineFromExpr (m : Machine Ident Term) : CommandElabM PUnit := do
    -- First, generate the inductive types for the enumerated sets of the machine
    generateAbstractEnumeratedSets m
    -- Then scope all the sets, constants, properties and variables (without their typing infos)
    -- and generate a structure named `m.name`
    generateMachineStructure m λ fields vars vars_typ ↦
      -- Then make all the typing predicates, invariants and assertions in our environment
      withProps m.invariants λ invariants ↦
        withProps m.assertions λ assertions ↦ do
          let consts ← m.structConstsName
          let machName ← m.structName
          let invs ← m.structInvariantsName
          let asserts ← m.structAssertsName

          -- Finally, declare the structures in the global environment
          generateStructure consts #[] (mkSort 2) fields
          Meta.withLocalDecl (mkToParentName consts) .default (Expr.const consts []) (kind := .implDetail) λ consts ↦ do
            generateStructure machName #[] (mkSort 2) vars #[consts]
          Meta.withLocalDecl `mach .default (.const machName []) (kind := .implDetail) λ mach ↦ do
            generateInvariantStructure m (fields ++ vars) vars_typ mach invariants λ invariants ↦ do
              generateStructure invs #[mach] (mkSort 0) invariants.valuesArray
              Meta.withLocalDecl `invs .default (.app (.const invs []) mach) (kind := .implDetail) λ machInv ↦ do
                generateAssertionStructure m (fields ++ vars) invariants.valuesArray mach machInv assertions λ assertions ↦ do
                  generateStructure asserts #[mach, machInv] (mkSort 0) assertions.valuesArray

    return .unit

  private def makeObligations (m : Machine Ident Term) : CommandElabM (Array Obligation) := do
    -- Then check the substitutions of the initialisation and operations
    -- let subInit := m.initialisation.2.generateMetaSubstitution m
      -- Meta.liftMetaM ∘ Meta.mkLambdaFVars #[mach] =<< generateSubstitution m.initialisation.2

    -- Substitutions of type `(mach : Expr) → (f : Expr) → MetaM Expr`:
    -- * `mach` is a free variable of the type `Mach` of the machine (to carry around variables)
    -- * `f` must internally be a functional expression from `Mach` to `Prop` (an invariant or an assertion)
    --
    -- For example, the substitution `pre h : x ∈ INTEGER then x := x + 1 ‖ y := 0` should become
    -- the meta-expression (abusing notations)
    -- `λ (mach : Mach) (t : Expr) ↦ `(expr| (h : x ∈ INTEGER) → $t { $mach with x := $mach.x + 1, y := 0 })`
    --
    -- Is there a possibility that this representation does not work for some kind of substitution?


    let mut obligations : Array Obligation := #[]

    obligations ← obligations.push <$> liftTermElabM do
      -- # Assertions
      --   Aₘ /- ∧ Aᵤ -/                                       -- Parameter constraints
      -- ∧ Bₘ /- ∧ Bᵤ ∧ Bₛ ∧ Bᵢ₍₁₎ ∧ … ∧ Bᵢ₍ₙ₎ -/             -- Properties
      -- /- ∧ Iᵤ ∧ Jᵤ -/
      -- ∧ Iₘ ∧ Lₘ                                             -- Invariants
      -- ∧ Jₘ₍₁₎ ∧ … ∧ Jₘ₍ₖ₋₁₎                                 -- Previous assertions
      -- ──────────────────────────────────────────────────────────────────────────────────
      -- ⊢ Jₘ₍ₖ₎
      let thm ← Meta.withLocalDeclD `mach (.const (← m.structName) []) λ mach ↦ do
        Meta.withLocalDeclD `invs (← Meta.mkAppM (← m.structInvariantsName) #[mach]) λ invs ↦ do
          Meta.mkForallFVars #[mach, invs] (← Meta.mkAppM (← m.structAssertsName) #[mach, invs])

      pure {
        name := (← m.structAssertsName) ++ `satisfied
        description := "Assertions are satisfied"
        type := thm
      }

    -- # Invariants (initialisation)
    --   Aₘ /- ∧ Aᵤ -/                                       -- Parameter constraints
    -- ∧ Bₘ /- ∧ Bᵤ ∧ Bₛ ∧ Bᵢ₍₁₎ ∧ … ∧ Bᵢ₍ₙ₎ -/             -- Properties
    -- /- ∧ Iᵤ ∧ Jᵤ -/
    -- /- ∧ Iₛ ∧ Jₛ -/
    -- ──────────────────────────────────────────────────────────────────────────────────
    -- ⊢ Uₘ • Iₘ

    return obligations





  def elabMachineCore (name : Ident) (params : TSyntaxArray `ident) (cs : TSyntaxArray `B.clause) :
      CommandElabM PUnit := do
    let mut «sets» : Option (Array (Ident × Array Ident)) := .none
    let mut «concrete_constants» : Option (Array (Binding Ident Term)) := .none
    let mut «properties» : Option (Array (Ident × Term)) := .none
    -- let mut «more_properties» : Array (Ident × Term) := #[]
    let mut «abstract_variables» : Option (Array (Binding Ident Term)) := .none
    let mut «invariants» : Option (Array (Ident × Term)) := .none
    -- let mut «more_invariants» : Array (Ident × Term) := #[]
    let mut «initialisation» : Option (Σ k, Substitution Ident Term k) := .none
    let mut «assertions» : Option (Array (Ident × Term)) := .none
    let mut «operations» : Option (Array (Operation Ident Term)) := .none

    for clause in cs do match clause with
      | `(clause| sets%$tk $ss*) =>
        guardNone «sets» tk "sets"
        «sets» := ss.map set_decl.extractSets
      | `(clause| properties%$tk $ps*) =>
        guardNone «properties» tk "properties"
        «properties» := ps.map prop_decl.extract
      | `(clause| concrete_constants%$tk $ds:constant_decl*) =>
        guardNone «concrete_constants» clause "(concrete_)constants"
        «concrete_constants» := ds.map constant_decl.extractConst
      | `(clause| abstract_variables%$tk $vs:var_decl*) =>
        guardNone «abstract_variables» clause "(abstract_)variables"
        «abstract_variables» := vs.map var_decl.extractVar
      | `(clause| invariants%$tk $invs*) =>
        guardNone «invariants» tk "invariants"
        «invariants» := invs.map prop_decl.extract
      | `(clause| assertions%$tk $ass*) =>
        guardNone «assertions» tk "assertions"
        «assertions» := ass.map prop_decl.extract
      | `(clause| initialisation%$tk $sub) =>
        guardNone «initialisation» tk "initialisation"
        «initialisation» := elabSubstitution sub
      | `(clause| operations%$tk $ops:operation*) =>
        guardNone «operations» tk "operations"
        «operations» ← Option.some <$> ops.mapM (liftMacroM ∘ elabOperation)
      | _ => throwUnsupportedSyntax


    -- TODO: Check that the machine is syntactically valid before generating its POs
    if «abstract_variables».isSome && «initialisation».isNone then
      throwError "variables clause requires an initialisation clause"


    let «machine» : Machine Ident Term := {
      name
      parameters := #[]
      constraints := #[]
      sees := #[]
      «sets» := «sets».getD #[]
      «abstract_constants» := #[]
      «concrete_constants» := «concrete_constants».getD #[]
      «properties» := «properties».getD #[]
      includes := #[]
      uses := #[]
      «abstract_variables» := «abstract_variables».getD #[]
      «concrete_variables» := #[]
      «invariants» := «invariants».getD #[]
      «initialisation» := «initialisation».getD ⟨_, .identity⟩
      «assertions» := «assertions».getD #[]
      «operations» := «operations».getD #[]
    }

    elabMachineFromExpr «machine»
    let goals ← makeObligations «machine»

    do
      let mut message : MessageData := ""
      if !goals.isEmpty then
        for goal in goals do
          message := message ++ m!"• {goal}"
        logInfo message

    modifyEnv λ env ↦ obligations.addEntry env goals

    return .unit
  where
    guardNone {α} : Option α → Syntax → String → CommandElabM PUnit
      | .none, _, _ => pure .unit
      | .some _, stx, clause => throwErrorAt stx "Machine {name} already has a(n) {clause} clause declared"

  elab_rules : command
    | `(machine $name_and_params:machine_name $cs:clause* end) => do
      let `(machine_name| $name $[($params,*)]?) := name_and_params | unreachable!
      elabMachineCore name (params.getD <| .mk #[]).getElems cs
end B


----- TESTS

/-
namespace __Priv
  inductive Test.C.enum where | c₁ | c₂ | c₃
  structure Test.constants where
    {α : Type}
    A : Set α
    A_abs : A ∈ FIN₁ Set.univ
    {β : Type}
    B : Set β
    B_abs : B ∈ FIN₁ Set.univ
    C : Set Test.C.enum
    C_def : C = {.c₁, .c₂, .c₃}
    x : Set Int
    x_type : x ∈ 𝒫₁ NATURAL
    y : SetRel Int Int
    y_type : y ∈ x ⟶ 0..255
    x_eq : x = {0, 1, 2}
  structure Test extends Test.constants where
    z : Set Int
    a : Int
    b : Int
  structure Test.invariants (mach : Test) where
    z_type : mach.z ∈ 𝒫₁ NATURAL
    a_type : mach.a ∈ 0..min mach.z (by admit)
    b_type : mach.b ∈ NATURAL
    z_le : _root_.B.Builtins.min (dom mach.y) (by admit) ∈ mach.z
    b_ge : mach.b ≥ 0
  structure Test.assertions (mach : Test) (invs : mach.invariants) where
    z_sub : mach.z ⊆ NATURAL
  theorem Test.assertions' : ∀ {mach : Test}, (invs : mach.invariants) → mach.assertions invs := λ {mach} invs ↦ by
    -- START TEMPLATE
    let {α, A, A_abs, β, B, B_abs, C, C_def, x, x_type, y, y_type, x_eq, z, a, b} := mach
    let {z_type, a_type, b_type, z_le, b_ge} := invs
    clear mach invs
    refine ⟨?z_sub⟩ <;> dsimp only at z_type a_type b_type z_le b_ge ⊢
    -- END TEMPLATE
    admit
  theorem Test.init.invariants : ∀ {consts}, (Test.mk consts {0} 0 7).invariants := λ {consts} ↦ by
    -- START TEMPLATE
    let {α, A, A_abs, β, B, B_abs, C, C_def, x, x_type, y, y_type, x_eq} := consts
    clear consts
    refine ⟨?z_type, ?a_type, ?b_type, ?z_le, ?b_ge⟩ <;> dsimp only
    -- END TEMPLATE
    · admit
    · admit
    · admit
    · admit
    · admit
  theorem Test.step.invariants : ∀ {mach : Test}, mach.invariants → (h : mach.z ⊆ mach.x) → {mach with a := mach.a + 1, b := mach.a + 1}.invariants := λ {mach} invs h ↦ by
    -- START TEMPLATE
    let {α, A, A_abs, β, B, B_abs, C, C_def, x, x_type, y, y_type, x_eq, z, a, b} := mach
    let {z_type, a_type, b_type, z_le, b_ge} := invs
    clear mach invs
    refine ⟨?z_type, ?a_type, ?b_type, ?z_le, ?b_ge⟩ <;> dsimp only at z_type a_type b_type z_le b_ge h ⊢
    -- END TEMPLATE
    · admit
    · admit
    · admit
    · admit
    · admit
-/
