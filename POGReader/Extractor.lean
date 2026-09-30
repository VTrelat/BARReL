import POGReader.Parser

namespace B.POG
  /--
    Represents a goal of the form `name : ∀ vars, hyps → goal`.
  -/
  structure Goal : Type _ where
    name : String
    reason : String
    vars : Array (String × Syntax.Typ)
    -- hyps : Array Syntax.Term
    goal : Syntax.Term
  deriving Inhabited

  private def extractSetsAndHyps (defs : Array (Σ k, Schema.Define k)) : Array Schema.Set × Array Syntax.Term :=
    defs.foldl (init := (#[], #[])) λ (sets, terms) ↦ λ
      | ⟨.ctx, .ctx ss ts⟩
      | ⟨.lprp, .lprp ss ts⟩
      | ⟨.aprp, .aprp ss ts⟩
      | ⟨.imlprp, .imlprp ss ts⟩
      | ⟨.imprp, .imprp ss ts⟩
      | ⟨.inprp, .inprp ss ts⟩ => (sets ++ ss, terms ++ ts)
      | ⟨.seext, .seext ts⟩
      | ⟨.inv, .inv ts⟩
      | ⟨.inext, .inext ts⟩
      | ⟨.cst, .cst ts⟩
      | ⟨.mchcst, .mchcst ts⟩
      | ⟨.abs, .abs ts⟩
      | ⟨.imext, .imext ts⟩
      | ⟨.ass, .ass ts⟩ => (sets, terms ++ ts)
      | ⟨.sets, .sets ss⟩ => (sets ++ ss, terms)

  private def _root_.B.Syntax.Term.splitAnds : Syntax.Term → Array Syntax.Term
    | .and t₁ t₂ => t₁.splitAnds ++ t₂.splitAnds
    | t => #[t]

  private def _root_.B.Syntax.Term.normalize : Syntax.Term → Syntax.Term
    -- basic terms
    | .var v => .var v
    | .int n => .int n
    | .real q => .real q
    | .bool b => .bool b
    -- pairs
    | .maplet t₁ t₂ => .maplet t₁.normalize t₂.normalize
    -- arithmetic
    | .uminus t => .uminus t.normalize
    | .add t₁ t₂ => .add t₁.normalize t₂.normalize
    | .sub t₁ t₂ => .sub t₁.normalize t₂.normalize
    | .mul t₁ t₂ => .mul t₁.normalize t₂.normalize
    | .div t₁ t₂ => .div t₁.normalize t₂.normalize
    | .mod t₁ t₂ => .mod t₁.normalize t₂.normalize
    | .exp t₁ t₂ => .exp t₁.normalize t₂.normalize
    | .le t₁ t₂ => .le t₁.normalize t₂.normalize
    | .lt t₁ t₂ => .lt t₁.normalize t₂.normalize
    -- logic
    | .and t₁ t₂ => .and t₁.normalize t₂.normalize
    | .or t₁ t₂ => .or t₁.normalize t₂.normalize
    | .imp t₁ t₂ => t₁.normalize.splitAnds.foldr .imp t₂.normalize
    | .iff t₁ t₂ => .iff t₁.normalize t₂.normalize
    | .not t => .not t.normalize
    | .eq t₁ t₂ => .eq t₁.normalize t₂.normalize
    -- sets
    -- basic sets
    | .𝔹 => .𝔹
    | .ℤ => .ℤ
    | .ℝ => .ℝ
    -- set operations
    | .setminus t₁ t₂ => .setminus t₁.normalize t₂.normalize
    | .fin t => .fin t.normalize
    | .fin₁ t => .fin₁ t.normalize
    | .interval t₁ t₂ => .interval t₁.normalize t₂.normalize
    | .set xs ty => .set (xs.map normalize) ty
    | .subset t₁ t₂ => .subset t₁.normalize t₂.normalize
    | .mem t₁ t₂ => .mem t₁.normalize t₂.normalize
    | .collect vs t => .collect vs t.normalize
    | .pow t => .pow t.normalize
    | .pow₁ t => .pow₁ t.normalize
    | .cprod t₁ t₂ => .cprod t₁.normalize t₂.normalize
    | .union t₁ t₂ => .union t₁.normalize t₂.normalize
    | .inter t₁ t₂ => .inter t₁.normalize t₂.normalize
    | .card t => .card t.normalize
    -- relations
    | .rel t₁ t₂ => .rel t₁.normalize t₂.normalize
    | .inv t => .inv t.normalize
    | .id t => .id t.normalize
    | .image t₁ t₂ => .image t₁.normalize t₂.normalize
    -- functions
    | .dom t => .dom t.normalize
    | .ran t => .ran t.normalize
    | .app t₁ t₂ => .app t₁.normalize t₂.normalize
    | .lambda vs t₁ t₂ => .lambda vs t₁.normalize t₂.normalize
    | .«fun» t₁ t₂ isPartial => .«fun» t₁.normalize t₂.normalize isPartial
    | .injfun t₁ t₂ isPartial => .injfun t₁.normalize t₂.normalize isPartial
    | .surjfun t₁ t₂ isPartial => .surjfun t₁.normalize t₂.normalize isPartial
    | .bijfun t₁ t₂ isPartial => .bijfun t₁.normalize t₂.normalize isPartial
    | .min t => .min t.normalize
    | .max t => .max t.normalize
    -- quantifiers
    | .all vs t => .all vs t.normalize
    | .«exists» vs t  => .«exists» vs t.normalize
    | .codomSubtr t₁ t₂ => .codomSubtr t₁.normalize t₂.normalize
    | .codomRestr t₁ t₂ => .codomRestr t₁.normalize t₂.normalize
    | .domSubtr t₁ t₂ => .domSubtr t₁.normalize t₂.normalize
    | .domRestr t₁ t₂ => .domRestr t₁.normalize t₂.normalize
    | .overload t₁ t₂ => .overload t₁.normalize t₂.normalize
    | .seq E => .seq E.normalize
    | .size E => .size E.normalize

  def extractGoals (pos : Schema.ProofObligations) : Array Goal :=
    pos.obligations.flatMap λ obligation ↦
      let uses : Array (Σ k, Schema.Define k) := obligation.uses.map λ k ↦ ⟨k, pos.defines.get! k⟩
      -- let uses := pos.defines.filter λ k _ ↦ obligation.uses.contains k
      let (sets, hyps₂) := extractSetsAndHyps uses
      let hyps₁ := sets.map λ set ↦
        if set.values.isEmpty then
          .mem (.var set.name) <| .fin₁ .ℤ
        else
          .and
            (.eq (.var set.name) (.set (set.values.map .var) (.pow .int))) -- S = {v₁, v₂, ...}
            (.not (.eq
              (.bijfun (.var set.name) (.interval (.int 1) (.int set.values.size)) (isPartial := false))
              (.set #[] (.pow (.pow (.prod .int .int)))))) -- S >->> 1..n ≠ ∅
      let hyps₃ := obligation.hypotheses

      obligation.simpleGoals.map λ goal ↦
        let hyps₄ := goal.refHyps.map λ i ↦ obligation.localHyps[i]!

        let name := obligation.name -- NOTE: do something with `goal.name`?
        let reason := goal.name

        {
          name
          reason
          vars := pos.vars
          goal := Syntax.Term.normalize <| (hyps₁ ++ hyps₂ ++ hyps₃ ++ hyps₄).foldr .imp goal.goal
        }
end B.POG
