import Barrel.Builtins.Init
import Barrel.Builtins.Relation
import Batteries.Tactic.GeneralizeProofs
import Barrel.Tactics

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

  structure app.WD {α : Type _} {β : Type _} (f : SetRel α β) (x : α) : Prop where
    isPartialFunction : f ∈ dom f ⟶ ran f
    isInDomain : x ∈ dom f

  noncomputable abbrev app {α β : Type _} (f : SetRel α β) (x : α) (wd : app.WD f x) : β :=
    Classical.choose wd.isInDomain
  scoped notation:290 F:290 "(" x:min ")'" wd:300 => app F x wd

  section Lemmas

    @[grind ., pfun]
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

    @[grind ., tfun]
    theorem tfun_of_singleton {α β : Type _} {a : α} {b : β} :
        {(a, b)} ∈ {a} ⟶ {b} := by
      constructor
      · exact pfun_of_singleton
      · rintro _ rfl
        exists b

    @[grind <=, pfun]
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

    @[pfun]
    theorem pfun.of_tfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⟶ B) : f ∈ A ⇸ B := hf.1
    @[pfun]
    theorem pfun.of_injpfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⤔ B) : f ∈ A ⇸ B := hf.1
    @[pfun]
    theorem pfun.of_surjpfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⤀ B) : f ∈ A ⇸ B := hf.1
    @[pfun]
    theorem pfun.of_bijpfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⤗ B) : f ∈ A ⇸ B := hf.1.1

    @[tfun]
    theorem tfun.of_injtfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ↣ B) : f ∈ A ⟶ B := hf.2
    @[tfun]
    theorem tfun.of_surjtfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ↠ B) : f ∈ A ⟶ B := hf.2
    @[tfun]
    theorem tfun.of_bijtfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⤖ B) : f ∈ A ⟶ B := hf.1.2

    @[wd_app]
    theorem app.WD_of_mem_pfun {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α} (hf : f ∈ A ⇸ B) (hA : A ⊆ dom f) (hx : x ∈ A) :
      app.WD f x where
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

    @[wd_app]
    theorem app.WD_of_mem_dom_pfun {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α} (hf : f ∈ A ⇸ B) (hx : x ∈ dom f) :
      app.WD f x where
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

    @[wd_app]
    theorem app.WD_of_mem_tfun {α β : Type _} {f : SetRel α β} {A : Set α} {B : Set β} {x : α}
      (hf : f ∈ A ⟶ B) (hx : x ∈ A) :
        app.WD f x := by
      apply app.WD_of_mem_pfun hf.1 (fun y hy ↦ ?_) hx
      · obtain ⟨z, -, hfxy⟩ := hf.2 y hy
        exact ⟨z, hfxy⟩

    @[grind →, simp]
    theorem app.of_pair_eq {α β : Type _} {f : SetRel α β} {x : α} {y : β}
      (wd : WD f x) (hxy : (x, y) ∈ f) :
        app f x wd = y :=
          wd.isPartialFunction.1.2 hxy (Classical.choose_spec wd.isInDomain) |>.symm

    @[grind →]
    theorem app.pair_app_mem {α β : Type _} {f : SetRel α β} {x : α} {wd : WD f x} :
      (x, f(x)'wd) ∈ f := Classical.choose_spec wd.isInDomain

    @[grind =>, simp]
    theorem app.of_pair_iff {α β : Type _} {f : SetRel α β} {x : α} {y : β}
      (wd : WD f x) :
        (x, y) ∈ f ↔ app f x wd = y where
      mp hxy := app.of_pair_eq wd hxy
      mpr h_eq := by
        rw [←h_eq]
        exact pair_app_mem

    @[simp]
    theorem tfun_dom_eq {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β} (hf : f ∈ A ⟶ B) :
      dom f = A := by
        ext x
        constructor <;> intro h
        · obtain ⟨_, hy⟩ := h
          exact mem_of_pair_mem_rel hf.1.1 hy |>.1
        · obtain ⟨_, -, hy⟩ := hf.2 x h
          exact mem_dom_of_pair_mem hy

    theorem pfun.dom_subset {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⇸ B) : dom f ⊆ A := by
      intro x ⟨y, hy⟩
      exact hf.1 hy |>.1

    @[tfun]
    theorem tfun.of_pfun {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⇸ B) : f ∈ dom f ⟶ ran f := by
      constructor
      · constructor
        · grind only [→ app.of_pair_eq, = Set.subset_def, = Set.mem_powerset_iff, = Set.mem_prod,
          = Set.setOf_true, → app.pair_app_mem, = app.of_pair_iff, usr Set.mem_setOf_eq,
          = Set.setOf_false, → mem_dom_of_pair_mem, cases eager Prod]
        · exact hf.2
      · rintro x ⟨y, hy⟩
        exists y
        and_intros
        · exists x
        · exact hy

    @[mono]
    theorem rel.mono {α β : Type _} {A C : Set α} {B D : Set β}
        (hAC : A ⊆ C) (hBD : B ⊆ D) : A ⟷ B ⊆ C ⟷ D := by
      rintro f hf ⟨x, y⟩ hxy
      and_intros
      · exact hf hxy |>.1 |> hAC
      · exact hf hxy |>.2 |> hBD

    @[mono]
    theorem pfun.mono {α β : Type _} {A C : Set α} {B D : Set β}
        (hAC : A ⊆ C) (hBD : B ⊆ D) : A ⇸ B ⊆ C ⇸ D :=
      fun _ ↦ And.imp (fun x ↦ rel.mono hAC hBD x) _root_.id

    theorem tfun.ran_subset {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
      (hf : f ∈ A ⟶ B) : ran f ⊆ B := by
      intro y ⟨x, hx⟩
      exact hf.1.1 hx |>.2

    @[mono]
    theorem tfun.range_mono {α β : Type _} {A : Set α} {B C : Set β}
        (hBC : B ⊆ C) : tfun A B ⊆ tfun A C := by
      intro f hf
      constructor
      · exact pfun.mono (subset_refl _) hBC (Set.mem_of_mem_inter_left hf)
      · intro x hx
        obtain ⟨y, hy, mem_f⟩ := hf.2 x hx
        use y, hBC hy, mem_f

    theorem tfun_iff {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β} :
        f ∈ A ⟶ B ↔ f ∈ A ⟷ B ∧ ∀ x ∈ A, ∃! y ∈ B, (x, y) ∈ f := by
      constructor
      · rintro ⟨⟨rel, isfunc⟩, tfun⟩
        and_intros
        · exact rel
        · intro x hx
          obtain ⟨y, hy, mem_f⟩ := tfun x hx
          exists y
          constructor
          · exact ⟨hy, mem_f⟩
          · rintro z ⟨hz, mem_f'⟩
            exact isfunc mem_f' mem_f
      · rintro ⟨rel, h⟩
        and_intros
        · exact rel
        · intro x y z hxy hxz
          apply h x (rel hxy).1 |>.unique
          · exact ⟨(rel hxy).2, hxy⟩
          · exact ⟨(rel hxz).2, hxz⟩
        · intro x hx
          obtain ⟨y, ⟨hy, mem_f⟩, unq⟩ := h x hx
          exists y

    theorem tfun_dom_ran_of_tfun {α} {β} {A : Set α} {B : Set β} {f : SetRel α β} (hf : f ∈ A ⟶ B) :
      f ∈ dom f ⟶ ran f := by
      rw [tfun_iff]
      and_intros
      · rintro ⟨x, y⟩ h
        exact ⟨⟨y, h⟩, ⟨x, h⟩⟩
      · rintro x ⟨y, h⟩
        exists y, ⟨⟨x, h⟩, h⟩
        rintro y' ⟨-, h'⟩
        exact hf.1.2 h' h

    @[wd_app]
    theorem app.WD_of_tfun_tfun {α} {β} {δ} {A : Set α} {B : Set β} {C : Set δ}
      {f : SetRel α (SetRel β δ)} (hf : f ∈ A ⟶ (B ⟶ C)) {x : α} (hx : x ∈ A) {y : β} (hy : y ∈ B) :
      app.WD (f(x)'(app.WD_of_mem_tfun hf hx)) y :=
        app.WD_of_mem_tfun (hf.1.1 (app.pair_app_mem (wd := app.WD_of_mem_tfun hf hx))).2 hy

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

    @[pfun]
    theorem pfun_of_overload {α β : Type _} {A C : Set α} {B D : Set β} {f₁ f₂ : SetRel α β}
      (hf₁ : f₁ ∈ A ⇸ B) (hf₂ : f₂ ∈ C ⇸ D) :
        f₁ <+ f₂ ∈ (A ∪ C) ⇸ (B ∪ D) := by
      and_intros
      · rintro ⟨x, y⟩ hxy
        simp only [overload, Set.mem_setOf, not_exists] at hxy
        obtain ⟨mem_f₁, notmem_f₂⟩ | mem_f₂ := hxy
        · and_intros
          · left
            exact mem_of_pair_mem_rel hf₁.1 mem_f₁ |>.1
          · left
            exact mem_of_pair_mem_rel hf₁.1 mem_f₁ |>.2
        · and_intros
          · right
            exact mem_of_pair_mem_rel hf₂.1 mem_f₂ |>.1
          · right
            exact mem_of_pair_mem_rel hf₂.1 mem_f₂ |>.2
      · intro x y z hxy hxz
        simp only [overload, Set.mem_setOf, not_exists] at hxy hxz
        obtain ⟨mem_f₁, notmem_f₂⟩ | mem_f₂ := hxy
        · obtain ⟨mem_f₁', notmem_f₂'⟩ | mem_f₂' := hxz
          · exact hf₁.2 mem_f₁ mem_f₁'
          · nomatch notmem_f₂ _ mem_f₂'
        · obtain ⟨mem_f₁', notmem_f₂'⟩ | mem_f₂' := hxz
          · nomatch notmem_f₂' _ mem_f₂
          · exact hf₂.2 mem_f₂ mem_f₂'

    @[wd_app]
    theorem app.WD_of_overload {α β : Type _} {A C : Set α} {B D : Set β} {f₁ f₂ : SetRel α β}
      {x : α} (hf₁ : f₁ ∈ A ⇸ B) (hf₂ : f₂ ∈ C ⇸ D) (hx : x ∈ dom f₁ ∨ x ∈ dom f₂) :
        app.WD (f₁ <+ f₂) x := by
      obtain hx | hx := hx <;> {
        apply app.WD_of_mem_dom_pfun
        · apply pfun_of_overload hf₁ hf₂
        · rw [overload_dom_eq]
          grind
      }

    @[tfun]
    theorem tfun_of_overload {α β : Type _} {A C : Set α} {B D : Set β} {f g : SetRel α β}
      (hf : f ∈ A ⟶ B) (hg : g ∈ C ⟶ D) :
        f <+ g ∈ (A ∪ C) ⟶ (B ∪ D) := by
      refine ⟨pfun_of_overload hf.1 hg.1, ?_⟩
      rintro x hx
      by_cases x_dom : x ∈ dom g
      · obtain ⟨y, hy⟩ := x_dom
        exists y, ?_ <;> right
        · exact mem_of_pair_mem_rel hg.1.1 hy |>.2
        · exact hy
      · rw [tfun_dom_eq hg] at x_dom
        replace hx := Or.resolve_right hx x_dom
        rw [←tfun_dom_eq hf] at hx
        obtain ⟨y, hy⟩ := hx
        exists y, ?_ <;> left
        · exact mem_of_pair_mem_rel hf.1.1 hy |>.2
        · rw [tfun_dom_eq hg]
          exact ⟨hy, x_dom⟩

  @[grind =, simp]
  theorem app.image_singleton_eq_of_wd {α β : Type _} {f : SetRel α β} {a : α} (wd : WD f a) :
      f[{a}] = {f(a)'wd} := by
    ext y
    simp only [SetRel.mem_image, Set.mem_singleton_iff, exists_eq_left]
    constructor
    · intro h
      symm
      exact of_pair_eq wd h
    · rintro rfl
      exact pair_app_mem

  @[grind =>, mono]
  theorem image_mono {α β : Type _} {f : SetRel α β} {A C : Set α}
    (hAC : A ⊆ C) : f[A] ⊆ f[C] := by
      intro y hy
      rw [SetRel.mem_image] at hy
      obtain ⟨x, hxA, hyf⟩ := hy
      exists x, hAC hxA

  @[simp]
  theorem app.image_singleton_eq_of_tfun {α β : Type _} {A : Set α} {B : Set β}
    {f : SetRel α β} {a : α} (hf : f ∈ A ⟶ B) (ha : a ∈ A) :
      f[{a}] = {f(a)'(WD_of_mem_tfun hf ha)} := app.image_singleton_eq_of_wd _

  @[simp]
  theorem app.image_singleton_eq_of_pfun_mem_dom {α β : Type _} {A : Set α} {B : Set β}
    {f : SetRel α β} {a : α} (hf : f ∈ A ⇸ B) (ha : a ∈ dom f) :
      f[{a}] = {f(a)'(WD_of_mem_dom_pfun hf ha)} := app.image_singleton_eq_of_wd _

  @[grind →]
  theorem app.mem_ran {α β : Type _} {f : SetRel α β} {x : α} (hx : WD f x) : f(x)'hx ∈ ran f :=
    ⟨x, pair_app_mem⟩

  theorem tfun.ran_eq {α β : Type _} {A : Set α} {B : Set β} {f : SetRel α β}
    (hf : f ∈ A ⟶ B) :
      ran f = f[A] := by
    ext y
    constructor <;> intro h
    · obtain ⟨x, hx⟩ := h
      exists x, hf.1.1 hx |>.1
    · rw [SetRel.mem_image] at h
      obtain ⟨x, hx, mem_f⟩ := h
      exists x

  end Lemmas

  section
    open Lean

    macro:289 "𝜆" "(" xs:ident,+ ")" " • " "(" h:(binderIdent " : ")? P:term " | " F:term ")" : term => do
      let xs : TSyntaxArray `ident := xs.getElems
      let y : TSyntax `ident := Lean.mkCIdent `y
      let tup : TSyntax `term ← xs[1:].foldlM (init := ← `(term| $(xs[0]!):ident)) λ acc x ↦ `(term| ($acc, $x:ident))
      match h with
      | .none => `({ ($tup, $y:ident) | $P ∧' $y:ident = $F })
      | .some h =>
        let h : TSyntax ``binderIdent := ⟨h.raw[0]⟩
        `({ ($tup, $y:ident) | ($h : $P) ∧' $y:ident = $F })

    private partial def unexpandLambda.getVars : TSyntax `term → Option (Array (TSyntax `ident))
      | `(term| $x:ident) => .some #[x]
      | `(term| ($t:term, $x:ident)) => unexpandLambda.getVars t |>.map (·.push x)
      | _ => none

    @[app_unexpander setOf] meta def unexpandLambda : Lean.PrettyPrinter.Unexpander
      | `($_ fun $z₁:ident => match $z₂:ident with | ($tup, $y₁:ident) => $P:term ∧' $y₂:ident = $F:term) => do
        go z₁ z₂ y₁ y₂ tup .none P F
      | `($_ fun $z₁:ident => match $z₂:ident with | ($tup, $y₁:ident) => ($h:binderIdent : $P:term) ∧' $y₂:ident = $F:term) => do
        go z₁ z₂ y₁ y₂ tup (.some h) P F
      | _ => throw ()
    where
      go z₁ z₂ y₁ y₂ tup (h : Option (TSyntax ``binderIdent)) P F := do
        if z₁ == z₂ && y₁ == y₂ then
          if let .some vars := unexpandLambda.getVars tup then
            match h with
            | .none => `(𝜆 ($vars,*) • ($P:term | $F))
            | .some h => `(𝜆 ($vars,*) • ($h : $P:term | $F))
          else
            throw ()
        else
          throw ()
  end
end B.Builtins
