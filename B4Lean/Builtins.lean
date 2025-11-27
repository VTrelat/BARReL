import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

namespace B.Builtins
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

  abbrev POW₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ 𝒫 A | S ≠ ∅ }

  abbrev rels {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    { R : Set (α × β) | ∀ x ∈ R, x.1 ∈ A ∧ x.2 ∈ B }

  abbrev pfun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    { f : Set (α × β) | f ∈ rels A B ∧ ∀ ⦃x y z⦄, (x, y) ∈ f → (x, z) ∈ f → y = z }

  abbrev tfun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ x ∈ A, ∃ y ∈ B, (x, y) ∈ f }

  abbrev injPFun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ ⦃x₁ x₂ y⦄, (x₁, y) ∈ f → (x₂, y) ∈ f → x₁ = x₂ }

  abbrev injTFun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    injPFun A B ∩ tfun A B

  abbrev surjPFun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    { f : Set (α × β) | f ∈ pfun A B ∧ ∀ y ∈ B, ∃ x ∈ A, (x, y) ∈ f }
  abbrev surjTFun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    surjPFun A B ∩ tfun A B

  abbrev bijFun {α β : Type _} (A : Set α) (B : Set β) : Set (Set (α × β)) :=
    injTFun A B ∩ surjTFun A B


  /-!
    # Function and relation operators
  -/

  open Classical in
  noncomputable abbrev app {α β : Type _} [Inhabited β] (f : Set (α × β)) (x : α) : β :=
    if h : ∃ y, (x, y) ∈ f then Classical.choose h else default



  /-!
    # Sets operators
  -/

  def interval (lo hi : Int) : Set Int := { n | lo ≤ n ∧ n ≤ hi }

  ----- Notations

  scoped notation "ℕ" => NATURAL
  scoped notation "ℕ₁" => NATURAL₁
  scoped notation "ℤ" => INTEGER
  scoped notation "ℝ" => REAL
  scoped notation "𝔹" => BOOL
  scoped prefix:250 "𝒫₁ " => POW₁

  scoped infixl:125 " ↔ " => rels
  scoped infixl:125 " ⇸ " => pfun
  scoped infixl:125 " ⟶ " => tfun
  scoped infixl:125 " ⤔ " => injPFun
  scoped infixl:125 " ↣ " => injTFun
  scoped infixl:125 " ⤀ " => surjPFun
  scoped infixl:125 " ↠ " => surjTFun
  scoped infixl:125 " ⤖ " => bijFun




  scoped infixl:170 ".." => interval


  scoped notation F:300 "(" x:min ")" => app F x

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
