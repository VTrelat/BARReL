import Lean.Message
open Lean

namespace B
  -- TODO: embed typing information directly into the AST?
  inductive Binding.Kind | eq | in
  deriving Repr, Inhabited

  structure Binding (α β : Type _) where
    name : α
    kind : Binding.Kind
    type : β
  deriving Repr, Inhabited

  inductive Substitution.Kind | level1 | any
  deriving Repr

  inductive Substitution (α β : Type _) : Substitution.Kind → Type
    | block {k} : Substitution α β k → Substitution α β .level1
    | identity : Substitution α β .level1
    | become_equal₁ : Array α → Array β → Substitution α β .level1
    | become_equal₂ : α → Array β → β → Substitution α β .level1
    | precond {k} : Array (α × β) → Substitution α β k → Substitution α β .level1
    | assert {k} : Array (α × β) → Substitution α β k → Substitution α β .level1
    | choice : Array (Σ k, Substitution α β k) → Substitution α β .level1
    | if : Array (β × Σ k, Substitution α β k) → Option (Σ k, Substitution α β k) → Substitution α β .level1
    | select : Array (β × Σ k, Substitution α β k) → Option (Σ k, Substitution α β k) → Substitution α β .level1
    -- case
    | any {k} : Array (Binding α β) → Array (α × β) → Substitution α β k → Substitution α β .level1
    | let {k} : Array α → Array (α × β) → Substitution α β k → Substitution α β .level1
    | become_element : Array α → β → Substitution α β .level1
    | become_such_that : Array α → β → Substitution α β .level1
    | var {k} : Array (Binding α β) → Substitution α β k → Substitution α β .level1
    -- call
    | seq {k₁ k₂} : Substitution α β k₁ → Substitution α β k₂ → Substitution α β .any
    | par {k₁ k₂} : Substitution α β k₁ → Substitution α β k₂ → Substitution α β .any
  deriving Repr

  instance {α β} {k} : Inhabited (Substitution α β k) := match k with
    | .level1 => ⟨.identity⟩
    | .any => ⟨.seq .identity .identity⟩
  instance {α β} : Inhabited (Σ k, Substitution α β k) := ⟨⟨.level1, .identity⟩⟩

  structure Operation (α β : Type _) where
    bound : Array α -- here?
    name : α
    params : Array (Binding α β)
    subst : Substitution α β .level1
  deriving Repr, Inhabited

  /-- Abstract machine -/
  structure Machine (α β : Type _) where
    name : α
    parameters : Array (α ⊕ Binding α β)
    constraints : Array (α × β)
    sees : Array α
    sets : Array (α × Array α)
    abstract_constants : Array (Binding α β)
    concrete_constants : Array (Binding α β)
    properties : Array (α × β)
    includes : Array (α × Array β)
    uses : Array α
    abstract_variables : Array (Binding α β)
    concrete_variables : Array (Binding α β)
    invariants : Array (α × β)
    initialisation : Σ k, Substitution α β k
    assertions : Array (α × β)
    operations : Array (Operation α β)
  deriving Repr
end B
