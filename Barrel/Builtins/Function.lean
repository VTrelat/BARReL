import Barrel.Builtins.Init
import Barrel.Builtins.Relation
import Batteries.Tactic.GeneralizeProofs

namespace B.Builtins
  abbrev pfun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ A ⟷ B ∧ ∀ ⦃x y z⦄, (x, y) ∈ f → (x, z) ∈ f → y = z }
  scoped infixl:125 " ⇸ " => pfun

  abbrev tfun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ A ⇸ B ∧ ∀ x ∈ A, ∃ y ∈ B, (x, y) ∈ f }
  scoped infixl:125 " ⟶ " => tfun

  abbrev injPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ A ⇸ B ∧ ∀ ⦃x₁ x₂ y⦄, (x₁, y) ∈ f → (x₂, y) ∈ f → x₁ = x₂ }
  scoped infixl:125 " ⤔ " => injPFun

  abbrev injTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    A ⤔ B ∩ A ⟶ B
  scoped infixl:125 " ↣ " => injTFun

  abbrev surjPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ A ⇸ B ∧ ∀ y ∈ B, ∃ x ∈ A, (x, y) ∈ f }
  scoped infixl:125 " ⤀ " => surjPFun

  abbrev surjTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    A ⤀ B ∩ A ⟶ B
  scoped infixl:125 " ↠ " => surjTFun

  abbrev bijPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    A ⤔ B ∩ A ⤀ B
  scoped infixl:125 " ⤗ " => bijPFun

  abbrev bijTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    A ↣ B ∩ A ↠ B
  scoped infixl:125 " ⤖ " => bijTFun

  structure app.WF {α : Type _} {β : Type _} (f : SetRel α β) (x : α) : Prop where
    isPartialFunction : f ∈ dom f ⟶ ran f
    isInDomain : x ∈ dom f

  noncomputable abbrev app {α β : Type _} (f : SetRel α β) (x : α) (wf : app.WF f x) : β :=
    Classical.choose wf.isInDomain
  scoped notation:290 F:290 "(" x:min ")'" wf:300 => app F x wf

  section Lemmas

    @[grind .]
    theorem pfun_of_singleton {α β : Type _} {a : α} {b : β} :
        {(a, b)} ∈ {a} ⇸ {b} := by
      and_intros
      · rintro ⟨x, y⟩ hxy
        rw [Set.mem_singleton_iff] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        trivial
      · intro x y z hxy hxz
        rw [Set.mem_singleton_iff] at hxy hxz
        obtain ⟨rfl, rfl⟩ := hxy
        obtain ⟨rfl, rfl⟩ := hxz
        rfl

    @[grind .]
    theorem tfun_of_singleton {α β : Type _} {a : α} {b : β} :
        {(a, b)} ∈ {a} ⟶ {b} := by
      constructor
      · exact pfun_of_singleton
      · rintro _ rfl
        exists b

    @[grind .]
    theorem pfun_singleton {α β : Type _} {a : α} {b : β} {A : Set α} {B : Set β}
      (ha : a ∈ A) (hb : b ∈ B) :
        {(a, b)} ∈ A ⇸ B := by
      and_intros
      · rintro ⟨x, y⟩ hxy
        rw [Set.mem_singleton_iff] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        trivial
      · intro x y z hxy hxz
        rw [Set.mem_singleton_iff] at hxy hxz
        obtain ⟨rfl, rfl⟩ := hxy
        obtain ⟨rfl, rfl⟩ := hxz
        rfl

    theorem app.WF_of_mem_pfun {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α} (hf : f ∈ A ⇸ B) (hA : A ⊆ dom f) (hx : x ∈ A) :
      app.WF f x where
      isPartialFunction := by
        obtain ⟨f_rel, f_is_func⟩ := hf
        and_intros
        · rintro ⟨x, y⟩ hxy
          and_intros
          · exists y
          · exists x
        · exact fun _ _ _ ↦ (f_is_func · ·)
        · intro x hx
          obtain ⟨y, hxy⟩ := hx
          refine ⟨y, ?_, hxy⟩
          rw [Set.mem_setOf]
          exists x
      isInDomain := hA hx

    theorem app.WF_of_mem_dom_pfun {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α} (hf : f ∈ A ⇸ B) (hx : x ∈ dom f) :
      app.WF f x where
      isPartialFunction := by
        obtain ⟨f_rel, f_is_func⟩ := hf
        and_intros
        · rintro ⟨x, y⟩ hxy
          and_intros
          · exists y
          · exists x
        · exact fun _ _ _ ↦ (f_is_func · ·)
        · intro x hx
          obtain ⟨y, hxy⟩ := hx
          refine ⟨y, ?_, hxy⟩
          rw [Set.mem_setOf]
          exists x
      isInDomain := hx

    theorem app.WF_of_mem_tfun {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α}
      (hf : f ∈ A ⟶ B) (hx : x ∈ A) :
        app.WF f x := by
      apply app.WF_of_mem_pfun hf.1 (fun y hy ↦ ?_) hx
      · obtain ⟨z, -, hfxy⟩ := hf.2 y hy
        exact ⟨z, hfxy⟩

    @[grind →, simp]
    theorem app.of_pair_eq {α β : Type _} {f : SetRel α β} {x : α} {y : β}
      (wf : WF f x) (hxy : (x, y) ∈ f) :
        app f x wf = y :=
          wf.isPartialFunction.1.2 hxy (Classical.choose_spec wf.isInDomain) |>.symm

    @[grind →]
    theorem app.pair_app_mem {α β : Type _} {f : SetRel α β} {x : α} {wf : WF f x} :
      (x, f(x)'wf) ∈ f := Classical.choose_spec wf.isInDomain

    @[grind =, simp]
    theorem app.of_pair_iff {α β : Type _} {f : SetRel α β} {x : α} {y : β}
      (wf : WF f x) :
        (x, y) ∈ f ↔ app f x wf = y where
      mp hxy := app.of_pair_eq wf hxy
      mpr h_eq := by
        rw [←h_eq]
        exact pair_app_mem

    @[simp]
    theorem tfun_dom_eq {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β} (hf : f ∈ A ⟶ B) :
      dom f = A := by
        ext x
        constructor <;> intro h
        · obtain ⟨_, hy⟩ := h
          exact hf.1.1 _ hy |>.1
        · obtain ⟨_, -, hy⟩ := hf.2 x h
          exact mem_dom_of_pair_mem hy

    @[simp]
    theorem overload_dom_eq {α β : Type _} {R₁ R₂ : SetRel α β} :
        dom (R₁ <+ R₂) = dom R₁ ∪ dom R₂ := by
      ext x
      constructor <;> intro h
      · rw [Set.mem_setOf_eq] at h
        obtain ⟨y, hy⟩ := h
        rw [Set.mem_setOf_eq] at hy
        obtain ⟨mem_R₁, -⟩ | ⟨mem_R₂⟩ := hy
        · left
          exists y
        · right
          exists y
      · by_cases hx : x ∈ dom R₂
        · obtain ⟨y, hy⟩ := hx
          exists y
          right
          exact hy
        · obtain h | h := h
          · obtain ⟨y, hy⟩ := h
            rw [Set.mem_setOf_eq]
            exists y
            simp only [overload, Set.mem_setOf, not_exists]
            left
            and_intros
            · exact hy
            · simpa [Set.mem_setOf_eq, not_exists] using hx
          · nomatch hx h

    theorem pfun_of_overload {α β : Type _} {A C : Set α} {B D : Set β} {f₁ f₂ : SetRel α β}
      (hf₁ : f₁ ∈ A ⇸ B) (hf₂ : f₂ ∈ C ⇸ D) :
        f₁ <+ f₂ ∈ (A ∪ C) ⇸ (B ∪ D) := by
      and_intros
      · rintro ⟨x, y⟩ hxy
        simp only [overload, Set.mem_setOf, not_exists] at hxy
        obtain ⟨mem_f₁, notmem_f₂⟩ | mem_f₂ := hxy
        · and_intros
          · left
            exact hf₁.1 _ mem_f₁ |>.1
          · left
            exact hf₁.1 _ mem_f₁ |>.2
        · and_intros
          · right
            exact hf₂.1 _ mem_f₂ |>.1
          · right
            exact hf₂.1 _ mem_f₂ |>.2
      · intro x y z hxy hxz
        simp only [overload, Set.mem_setOf, not_exists] at hxy hxz
        obtain ⟨mem_f₁, notmem_f₂⟩ | mem_f₂ := hxy
        · obtain ⟨mem_f₁', notmem_f₂'⟩ | mem_f₂' := hxz
          · exact hf₁.2 mem_f₁ mem_f₁'
          · nomatch notmem_f₂ _ mem_f₂'
        · obtain ⟨mem_f₁', notmem_f₂'⟩ | mem_f₂' := hxz
          · nomatch notmem_f₂' _ mem_f₂
          · exact hf₂.2 mem_f₂ mem_f₂'

    theorem app.WF_of_overload {α β : Type _} {A C : Set α} {B D : Set β} {f₁ f₂ : SetRel α β}
      {x : α} (hf₁ : f₁ ∈ A ⇸ B) (hf₂ : f₂ ∈ C ⇸ D) (hx : x ∈ dom f₁ ∨ x ∈ dom f₂) :
        app.WF (f₁ <+ f₂) x := by
      obtain hx | hx := hx <;> {
        apply app.WF_of_mem_dom_pfun
        · apply pfun_of_overload hf₁ hf₂
        · rw [overload_dom_eq]
          grind
      }

    theorem tfun_of_overload {α β : Type _} {A C : Set α} {B D : Set β} {f g : SetRel α β}
      (hf : f ∈ A ⟶ B) (hg : g ∈ C ⟶ D) :
        f <+ g ∈ (A ∪ C) ⟶ (B ∪ D) := by
      refine ⟨pfun_of_overload hf.1 hg.1, ?_⟩
      rintro x hx
      by_cases x_dom : x ∈ dom g
      · obtain ⟨y, hy⟩ := x_dom
        exists y, ?_ <;> right
        · exact hg.1.1 _ hy |>.2
        · exact hy
      · rw [tfun_dom_eq hg] at x_dom
        replace hx := Or.resolve_right hx x_dom
        rw [←tfun_dom_eq hf] at hx
        obtain ⟨y, hy⟩ := hx
        exists y, ?_ <;> left
        · exact hf.1.1 _ hy |>.2
        · rw [tfun_dom_eq hg]
          exact ⟨hy, x_dom⟩

  end Lemmas

  section
    open Lean

    macro:289 "𝜆" "(" xs:ident,+ ")" " • " "(" P:term " | " F:term ")" : term => do
      let xs : TSyntaxArray `ident := xs.getElems
      let y : TSyntax `ident := Lean.mkCIdent `y
      let tup : TSyntax `term ← xs[1:].foldlM (init := ← `(term| $(xs[0]!):ident)) λ acc x ↦ `(term| ($acc, $x:ident))
      `({ ($tup, $y:ident) | $P ∧' $y:ident = $F })

    @[app_unexpander setOf] meta def unexpandLambda : Lean.PrettyPrinter.Unexpander
      | `($_ fun $z₁:ident => match $z₂:ident with | ($tup, $y₁:ident) => $P:term ∧' $y₂:ident = $F:term) => do
        if z₁ == z₂ && y₁ == y₂ then
          let rec getVars : TSyntax `term → Option (Array (TSyntax `ident))
            | `(term| $x:ident) => .some #[x]
            | `(term| ($t:term, $x:ident)) => getVars t |>.map (·.push x)
            | _ => throw ()
          if let .some vars := getVars tup then
            `(𝜆 ($vars,*) • ($P | $F))
          else
            throw ()
        else
          throw ()
      | _ => throw ()
  end
end B.Builtins
