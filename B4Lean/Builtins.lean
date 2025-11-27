import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import B.Syntax.Extra

namespace B.Builtins

  /-!
    # Builtin sets
  -/

  abbrev NAT : Set Int := { n | 0 ≤ n ∧ n ≤ B.MAXINT }
  abbrev NAT₁ : Set Int := { n | 1 ≤ n ∧ n ≤ B.MAXINT }
  abbrev NATURAL : Set Int := { n | 0 ≤ n }
  abbrev NATURAL₁ : Set Int := { n | 1 ≤ n }

  abbrev INT : Set Int := { n | MININT ≤ n ∧ n ≤ MAXINT }
  abbrev INTEGER : Set Int := Set.univ

  abbrev BOOL : Set Prop := Set.univ

  abbrev FLOAT : Set Float := Set.univ

  abbrev REAL : Set Real := Set.univ

  abbrev rels {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := { ⟨a, b⟩ : α × β | a ∈ A ∧ b ∈ B }

  abbrev pfun {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := sorry
  abbrev tfun {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := sorry

  abbrev injPFun {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := sorry
  abbrev injTFun {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := sorry

  abbrev surjPFun {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := sorry
  abbrev surjTFun {α β : Type _} (A : Set α) (B : Set β) : Set (α × β) := sorry

  /-!
    # Function and relation operators
  -/




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

  scoped infixl:125 "↔" => rels
  scoped infixl:125 "⇸" => pfun
  scoped infixl:125 "⟶" => tfun
  scoped infixl:125 "⤔" => injPFun
  scoped infixl:125 "↣" => injTFun
  scoped infixl:125 "⤀" => surjPFun
  scoped infixl:125 "↠" => surjTFun


  scoped infixl:170 ".." => interval



  /-
  Unicode characters

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
  `<->` ≔ `↔`
  `>->>` ≔ `⤖`
  `+->` ≔ `⇸`
  `>+>` ≔ `⤔`
  `>->` ≔ `↣`
  `+>>` ≔ `⤀`
  `->>` ≔ `↠`
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
  `..` ≔ `‥`
  `.` ≔ `·`
  `-` ≔ `−`
  `*` ≔ `∗`
  `/` ≔ `÷`
  `:=` ≔ `≔`
  `::` ≔ `:∈`
  `:|` ≔ `:∣`
  `:` ≔ `∈`
  `|` ≔ `∣`
  `,,` ≔ `↦`
  -/

end B.Builtins
