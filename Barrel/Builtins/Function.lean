import Barrel.Builtins.Relation

namespace B.Builtins
  abbrev pfun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ rels A B ∧ ∀ ⦃x y z⦄, (x, y) ∈ f → (x, z) ∈ f → y = z }
  scoped infixl:125 " ⇸ " => pfun

  abbrev tfun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ x ∈ A, ∃ y ∈ B, (x, y) ∈ f }
  scoped infixl:125 " ⟶ " => tfun

  abbrev injPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ ⦃x₁ x₂ y⦄, (x₁, y) ∈ f → (x₂, y) ∈ f → x₁ = x₂ }
  scoped infixl:125 " ⤔ " => injPFun

  abbrev injTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    injPFun A B ∩ tfun A B
  scoped infixl:125 " ↣ " => injTFun

  abbrev surjPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ y ∈ B, ∃ x ∈ A, (x, y) ∈ f }
  scoped infixl:125 " ⤀ " => surjPFun

  abbrev surjTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    surjPFun A B ∩ tfun A B
  scoped infixl:125 " ↠ " => surjTFun

  abbrev bijPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    injPFun A B ∩ surjPFun A B
  scoped infixl:125 " ⤗ " => bijPFun

  abbrev bijTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    injTFun A B ∩ surjTFun A B
  scoped infixl:125 " ⤖ " => bijTFun

  structure app.WF {α : Type _} {β : Type _} (f : SetRel α β) (x : α) : Prop where
    isPartialFunction : f ∈ pfun (dom f) (ran f)
    isInDomain : x ∈ dom f

  noncomputable abbrev app {α β : Type _} (f : SetRel α β) (x : α) (wf : app.WF f x): β :=
    Classical.choose wf.isInDomain
  scoped notation:290 F:290 "(" x:min ")'" wf:300 => app F x wf
end B.Builtins
