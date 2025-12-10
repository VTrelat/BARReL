import Mathlib.Data.Rel

namespace B.Builtins
  abbrev rels {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    𝒫 (A ×ˢ B)
    -- { R : Set (α × β) | ∀ x ∈ R, x.1 ∈ A ∧ x.2 ∈ B }
  scoped infixl:125 " ⟷ " => rels

  abbrev id {α : Type _} (A : Set α) : SetRel α α :=
    { (x, x) | x ∈ A }

  abbrev dom {α β : Type _} (R : SetRel α β) : Set α :=
    { x | ∃ y, (x, y) ∈ R }
  abbrev ran {α β : Type _} (R : SetRel α β) : Set β :=
    { y | ∃ x, (x, y) ∈ R }

  abbrev domRestr {α β : Type _} (E : Set α) (R : SetRel α β) : SetRel α β :=
    { z ∈ R | z.1 ∈ E }
  scoped infixl:160 " ◁ " => domRestr

  abbrev domSubtr {α β : Type _} (E : Set α) (R : SetRel α β) : SetRel α β :=
    { z ∈ R | z.1 ∉ E }
  scoped infixl:160 " ⩤ " => domSubtr

  abbrev codomRestr {α β : Type _} (R : SetRel α β) (E : Set β) : SetRel α β :=
    { z ∈ R | z.2 ∈ E }
  scoped infixl:160 " ▷ " => codomRestr

  abbrev codomSubtr {α β : Type _} (R : SetRel α β) (E : Set β) : SetRel α β :=
    { z ∈ R | z.2 ∉ E }
  scoped infixl:160 " ⩥ " => codomSubtr

  abbrev overload {α β : Type _} (R₁ : SetRel α β) (R₂ : SetRel α β) : SetRel α β :=
    { (x, y) | (x, y) ∈ R₁ ∧ x ∉ dom R₂ ∨ (x, y) ∈ R₂ }
  scoped infixl:160 " <+ " => overload

  scoped postfix:230 "⁻¹" => SetRel.inv
  scoped notation:290 R:290 "[" X:min "]" => SetRel.image R X

  section Lemmas
    @[grind →]
    theorem mem_dom_of_pair_mem {α β : Type _} {f : SetRel α β} {x : α} {y : β} (hxy : (x, y) ∈ f) :
      x ∈ dom f := ⟨y, hxy⟩

    theorem mem_of_pair_mem_rel {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α} {y : β} (hf : f ∈ A ⟷ B) (hxy : (x, y) ∈ f) :
        x ∈ A ∧ y ∈ B := by
      rw [Set.mem_powerset_iff] at hf
      exact hf hxy

    @[simp]
    theorem dom.of_empty {α β : Type _} : dom (∅ : SetRel α β) = ∅ := by
      simp only [dom, Set.mem_empty_iff_false, exists_false, Set.setOf_false]

    @[simp]
    theorem ran.of_empty {α β : Type _} : ran (∅ : SetRel α β) = ∅ := by
      simp only [ran, Set.mem_empty_iff_false, exists_false, Set.setOf_false]

  end Lemmas
end B.Builtins
