import Mathlib.Data.Set.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Real.Basic

namespace B.Builtins
  open Classical

  /--
    An opaque inhabitant of every type.

    In an ideal world, it would not be possible to reason on `Inhabited.default`.
    Unfortunately, it is possible to prove the goal `⊢ @Inhabited.default ℤ = 0`, which we
    actually don't want here.

    Instead, we introduce an opaque symbol `undefined`.
    The fact that it is opaque means that it cannot be unfolded at all, nor can
    any property be derived for it.

    If you are seeing `undefined` in your proof, and your hypotheses are not contradictory,
    then you must have done something wrong, or your goal is unprovable.
  -/
  noncomputable opaque undefined.{u} {α : Type u} [Inhabited α] : Nat → α

  /-!
    # Builtin sets
  -/

  abbrev MAXINT : Int := 2147483647
  abbrev MININT : Int := -2147483647

  abbrev NAT : Set Int := { n | 0 ≤ n ∧ n ≤ MAXINT }
  abbrev NAT₁ : Set Int := { n | 1 ≤ n ∧ n ≤ MAXINT }
  abbrev NATURAL : Set Int := { n | 0 ≤ n }
  abbrev NATURAL₁ : Set Int := { n | 1 ≤ n }

  abbrev INT : Set Int := { n | MININT ≤ n ∧ n ≤ MAXINT }
  abbrev INTEGER : Set Int := Set.univ

  abbrev BOOL : Set Prop := Set.univ

  abbrev FLOAT : Set Float := Set.univ

  abbrev REAL : Set Real := Set.univ

  abbrev POW₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ 𝒫 A | S.Nonempty }

  abbrev rels {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { R : Set (α × β) | ∀ x ∈ R, x.1 ∈ A ∧ x.2 ∈ B }

  abbrev pfun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ rels A B ∧ ∀ ⦃x y z⦄, (x, y) ∈ f → (x, z) ∈ f → y = z }

  abbrev tfun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ x ∈ A, ∃ y ∈ B, (x, y) ∈ f }

  abbrev injPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ ⦃x₁ x₂ y⦄, (x₁, y) ∈ f → (x₂, y) ∈ f → x₁ = x₂ }

  abbrev injTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    injPFun A B ∩ tfun A B

  abbrev surjPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ y ∈ B, ∃ x ∈ A, (x, y) ∈ f }
  abbrev surjTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    surjPFun A B ∩ tfun A B

  abbrev bijPFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    injPFun A B ∩ surjPFun A B

  abbrev bijTFun {α β : Type _} (A : Set α) (B : Set β) : Set (SetRel α β) :=
    injTFun A B ∩ surjTFun A B


  /-!
    # Function and relation operators
  -/

  abbrev id {α : Type _} (A : Set α) : SetRel α α :=
    { (x, x) | x ∈ A }

  abbrev dom {α β : Type _} (R : SetRel α β) : Set α :=
    { x | ∃ y, (x, y) ∈ R }
  abbrev ran {α β : Type _} (R : SetRel α β) : Set β :=
    { y | ∃ x, (x, y) ∈ R }

  structure app.WF {α : Type _} {β : Type _} (f : SetRel α β) (x : α) : Prop where
    isPartialFunction : f ∈ pfun (dom f) (ran f)
    isInDomain : x ∈ dom f

  noncomputable abbrev app {α β : Type _} (f : SetRel α β) (x : α) (wf : app.WF f x): β :=
    Classical.choose wf.isInDomain

  abbrev domRestr {α β : Type _} (R : SetRel α β) (E : Set α) : SetRel α β :=
    { z ∈ R | z.1 ∈ E }
  abbrev domSubtr {α β : Type _} (R : SetRel α β) (E : Set α) : SetRel α β :=
    { z ∈ R | z.1 ∉ E }
  abbrev codomRestr {α β : Type _} (R : SetRel α β) (E : Set β) : SetRel α β :=
    { z ∈ R | z.2 ∈ E }
  abbrev codomSubtr {α β : Type _} (R : SetRel α β) (E : Set β) : SetRel α β :=
    { z ∈ R | z.2 ∉ E }

  /-!
    # Sets operators
  -/

  abbrev interval (lo hi : Int) : Set Int := { n | lo ≤ n ∧ n ≤ hi }

  abbrev FIN {α : Type _} (A : Set α) : Set (Set α) := { S ⊆ A | S.Finite }
  abbrev FIN₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ FIN A | S.Nonempty }

  /-!
    # Arithmetic operators
  -/

  structure min.WF {α : Type _} [LinearOrder α] (S : Set α) : Prop where
    isBoundedBelow : ∃ x ∈ S, ∀ y ∈ S, x ≤ y

  noncomputable abbrev min {α : Type _} [LinearOrder α] (S : Set α) (wf : min.WF S) : α :=
    Classical.choose wf.isBoundedBelow

  structure max.WF {α : Type _} [LinearOrder α] (S : Set α) : Prop where
    isBoundedAbove : ∃ x ∈ S, ∀ y ∈ S, y ≤ x

  noncomputable abbrev max {α : Type _} [LinearOrder α] (S : Set α) (wf : max.WF S) : α :=
    Classical.choose wf.isBoundedAbove


  ----- Notations

  -- scoped notation "ℕ" => NATURAL
  -- scoped notation "ℕ₁" => NATURAL₁
  -- scoped notation "ℤ" => INTEGER
  -- scoped notation "ℝ" => REAL
  -- scoped notation "𝔹" => BOOL
  scoped prefix:250 "𝒫₁ " => POW₁

  scoped infixl:125 " ↔ " => rels
  scoped infixl:125 " ⇸ " => pfun
  scoped infixl:125 " ⟶ " => tfun
  scoped infixl:125 " ⤔ " => injPFun
  scoped infixl:125 " ↣ " => injTFun
  scoped infixl:125 " ⤀ " => surjPFun
  scoped infixl:125 " ↠ " => surjTFun
  scoped infixl:125 " ⤗ " => bijPFun
  scoped infixl:125 " ⤖ " => bijTFun

  scoped infixl:160 " ◁ " => domRestr
  scoped infixl:160 " ▷ " => codomRestr
  scoped infixl:160 " ⩤ " => domSubtr
  scoped infixl:160 " ⩥ " => codomSubtr



  scoped infixl:170 ".." => interval

  scoped postfix:230 "⁻¹" => SetRel.inv

  scoped notation:290 "min_@" n "(" S:min ")" => min n S
  scoped notation:290 "max_@" n "(" S:min ")" => max n S

  scoped notation:290 F:290 "(" x:min ")_@" n => app n F x
  scoped notation:290 R:290 "[" X:min "]" => SetRel.image R X
  /-
  TODO: add remaining Unicode characters

  `|>>` ≔ `⩥`
  `|>` ≔ `▷`
  `\/` ≔ `∪`
  `/\` ≔ `∩`
  `|->` ≔ `↦`
  `-->` ≔ `→`
  `/<<:` ≔ `⊄`
  `/<:` ≔ `⊈`
  `/:` ≔ `∉`
  `<=>` ≔ `⇔`
  `=>` ≔ `⇒`
  `&` ≔ `∧`
  `!` ≔ `∀`
  `#` ≔ `∃`
  `/=` ≔ `≠`
  `<=` ≔ `≤`
  `>=` ≔ `≥`
  `<<:` ≔ `⊂`
  `<:` ≔ `⊆`
  `{}` ≔ `∅`
  `\` ≔ `∖`
  `**` ≔ `×`
  `<+` ≔ `` (missing)
  `><` ≔ `⊗`
  `||` ≔ `∥`
  `~` ≔ `∼`
  `<<|` ≔ `⩤`
  `<|` ≔ `◁`
  `%` ≔ `λ`
  `.` ≔ `·`
  `-` ≔ `−`
  `*` ≔ `∗`
  `/` ≔ `÷`
  `:=` ≔ `≔`
  `::` ≔ `:∈`
  `:|` ≔ `:∣`
  `:` ≔ `∈`
  `|` ≔ `∣`

  -/

end B.Builtins
