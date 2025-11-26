import POGReader_.Parser

namespace B.POG
  /--
    Represents a goal of the form `name : ∀ vars, hyps → goal`.
  -/
  structure Goal : Type _ where
    name : String
    vars : Array (String × Syntax.Typ)
    hyps : Array Syntax.Term
    goal : Syntax.Term
  deriving Inhabited

  private def extractSetsAndHyps (defs : Std.DHashMap Schema.DefineType Schema.Define) : Array Schema.Set × Array Syntax.Term :=
    defs.fold (init := (#[], #[])) λ (sets, terms) ↦ λ
      | .ctx, .ctx ss ts
      | .lprp, .lprp ss ts
      | .aprp, .aprp ss ts
      | .imlprp, .imlprp ss ts
      | .imprp, .imprp ss ts
      | .inprp, .inprp ss ts => (sets ++ ss, terms ++ ts)
      | .seext, .seext ts
      | .inv, .inv ts
      | .inext, .inext ts
      | .cst, .cst ts
      | .mchcst, .mchcst ts
      | .abs, .abs ts
      | .imext, .imext ts
      | .ass, .ass ts => (sets, terms ++ ts)
      | .sets, .sets ss => (sets ++ ss, terms)

  def extractGoals (pos : Schema.ProofObligations) : Array Goal :=
    pos.obligations.flatMap λ obligation ↦
      let uses := pos.defines.filter λ k _ ↦ obligation.uses.contains k
      let (sets, hyps₁) := extractSetsAndHyps uses
      let hyps₂ := obligation.hypotheses
      let hyps₃ := sets.map λ set ↦ .eq (.var set.name) (.set <| set.values.map .var)

      obligation.simpleGoals.map λ goal ↦
        let hyps₄ := goal.refHyps.map λ i ↦ obligation.localHyps[i]!

        let name := obligation.name -- NOTE: do something with `goal.name`?

        {
          name
          vars := pos.vars
          hyps := hyps₁ ++ hyps₂ ++ hyps₃ ++ hyps₄
          goal := goal.goal
        }
end B.POG
