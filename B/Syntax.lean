import Extra.Prettifier
import Std.Data.HashSet

namespace B.Syntax
  inductive Typ : Type _
    | int | bool | real
    | pow : Typ → Typ
    | prod : Typ → Typ → Typ
    deriving DecidableEq, Inhabited, Repr

  private def Typ.toString : Typ → String
    | .int => "INT"
    | .bool => "BOOL"
    | .real => "REAL"
    | .pow t => "POW(" ++ toString t ++ ")"
    | .prod t1 t2 => "PROD(" ++ toString t1 ++ ", " ++ toString t2 ++ ")"

  instance : ToString Typ where
    toString := Typ.toString

  inductive Term : Type _ where
    -- basic terms
    | var (v : String)
    | int (n : Int)
    | bool (b : Bool)
    -- pairs
    | maplet (x y : Term)
    -- arithmetic
    | uminus (x : Term)
    | add (x y : Term)
    | sub (x y : Term)
    | mul (x y : Term)
    | div (x y : Term)
    | mod (x y : Term)
    | exp (x y : Term)
    | le (x y : Term)
    | lt (x y : Term)
    -- logic
    | and (x y : Term)
    | or (x y : Term)
    | imp (x y : Term)
    | iff (x y : Term)
    | not (x : Term)
    | eq (x y : Term)
    -- sets
    -- basic sets
    | 𝔹
    | ℤ
    | ℝ
    -- set operations
    | setminus (S T : Term)
    | fin (S : Term)
    | fin₁ (S : Term)
    | interval (lo hi : Term)
    | set (xs : Array Term) (ty : Typ)
    | subset (S T : Term)
    | mem (x : Term) (S : Term)
    | collect (vs : Array (String × Typ)) (P : Term)
    | pow (S : Term) | pow₁ (S : Term)
    | cprod (S T : Term)
    | union (S T : Term)
    | inter (S T : Term)
    | card (S : Term)
    -- relations
    | rel (A B : Term)
    | inv (R : Term)
    | id (A : Term)
    | image (R X : Term)
    | domRestr (R E : Term)
    | domSubtr (R E : Term)
    | codomRestr (R E : Term)
    | codomSubtr (R E : Term)
    -- functions
    | dom (f : Term)
    | ran (f : Term)
    | app (f x : Term)
    | lambda (vs : Array (String × Typ)) (D P : Term)
    | «fun» (A B : Term) (isPartial := true)
    | injfun (A B : Term) (isPartial := true)
    | surjfun (A B : Term) (isPartial := true)
    | bijfun (A B : Term) (isPartial := true)
    | min (S : Term)
    | max (S : Term)
    -- quantifiers
    | all (vs : Array (String × Typ)) (P : Term)
    | exists (vs : Array (String × Typ)) (P : Term)
    deriving Inhabited, Repr

  partial def Term.pretty : Term -> Nat -> Std.Format
    | .var v => λ _ => v
    | .int n => λ _ => toString n
    | .bool x => λ _ => toString x
    | .𝔹 => λ _ => "𝔹"
    | .ℤ => λ _ => "ℤ"
    | .ℝ => λ _ => "ℝ"
    | .uminus x => «prefix» Term.pretty 210 "−" x
    | .imp x y => «infixl» Term.pretty 30 "⇒" x y
    | .iff x y => «infixl» Term.pretty 30 "⇔" x y
    | .or x y => «infixl» Term.pretty 40 "∨" x y
    | .and x y => «infixl» Term.pretty 40 "∧" x y
    | .eq x y => «infixl» Term.pretty 60 "=" x y
    | .mem x S => «infixl» Term.pretty 120 "∈" x S
    | .subset S T => «infixl» Term.pretty 110 "⊆" S T
    | .rel A B => «infixl» Term.pretty 125 "↔" A B
    | .inv R => «postfix» Term.pretty 230 "⁻¹" R
    | .fun A B isPartial => «infixl» Term.pretty 125 (if isPartial then "⇸" else "⟶") A B
    | .injfun A B isPartial => «infixl» Term.pretty 125 (if isPartial then "⤔" else "↣") A B
    | .surjfun A B isPartial => «infixl» Term.pretty 125 (if isPartial then "⤀" else "↠") A B
    | .bijfun A B isPartial => «infixl» Term.pretty 125 (if isPartial then "⤗" else "⤖") A B
    | .le x y => «infixl» Term.pretty 160 "≤" x y
    | .lt x y => «infixl» Term.pretty 160 "<" x y
    | .inter x y => «infixl» Term.pretty 160 "∩" x y
    | .union x y => «infixl» Term.pretty 160 "∪" x y
    | .maplet x y => «infixl» Term.pretty 160 "↦" x y
    | .add x y => «infixl» Term.pretty 180 "+" x y
    | .sub x y => «infixl» Term.pretty 180 "-" x y
    | .setminus x y => «infixl» Term.pretty 180 "∖" x y
    | .mul x y => «infixl» Term.pretty 190 "*" x y
    | .exp x y => «infixr» Term.pretty 200 "^" x y
    | .div x y => «infixl» Term.pretty 190 "/" x y
    | .mod x y => «infixl» Term.pretty 190 "mod" x y
    | .cprod x y => «infixl» Term.pretty 190 "⨯" x y
    | .not x => «prefix» Term.pretty 250 "¬" x
    | .interval lo hi => «infixl» Term.pretty 170 ".." lo hi
    | .set xs _ =>
      let elems := xs.toList.map (fun x ↦ Term.pretty x 0 |> toString) |> String.intercalate ", "
      λ _ => "{ " ++ elems ++ " }"
    | .exists v P =>
      let vs := (v.map fun ⟨n, ty⟩ ↦ s!"{n} : {ty}").toList |> String.intercalate ", "
      binder Term.pretty 250 "∃ " vs ". " (.var "") "" P ""
    | .all v P =>
      let vs := (v.map fun ⟨n, ty⟩ ↦ s!"{n} : {ty}").toList |> String.intercalate ", "
      binder Term.pretty 250 "∀ " vs ". " (.var "") "" P ""
    | .collect v P =>
      let vs := (v.map fun ⟨n, ty⟩ ↦ s!"{n} : {ty}").toList |> String.intercalate ", "
      binder Term.pretty 250 "{ " vs " | " (.var "") "" P ""
    | .lambda v D P =>
      let vs := (v.map fun ⟨n, ty⟩ ↦ s!"{n} : {ty}").toList |> String.intercalate ", "
      binder Term.pretty 0 "λ " vs s!", " D " ⇒ " P ""
    | .app f x => λ _ => Term.pretty f 300 ++ .paren (Term.pretty x 0)
    | .pow S => «prefix» Term.pretty 250 "𝒫 " S
    | .pow₁ S => «prefix» Term.pretty 250 "𝒫₁ " S
    | .min S => «prefix» Term.pretty 250 "min " S
    | .max S => «prefix» Term.pretty 250 "max " S
    | .domRestr R E => «infixl» Term.pretty 160 "◁" R E
    | .domSubtr R E => «infixl» Term.pretty 160 "⩤" R E
    | .codomRestr R E => «infixl» Term.pretty 160 "▷" R E
    | .codomSubtr R E => «infixl» Term.pretty 160 "⩥" R E
    | .dom f => fun _ ↦ Term.pretty (.var "dom") 300 ++ .paren (Term.pretty f 0)
    | .ran f => fun _ ↦ Term.pretty (.var "ran") 300 ++ .paren (Term.pretty f 0)
    | .fin S => fun _ ↦ Term.pretty (.var "fin") 300 ++ .paren (Term.pretty S 0)
    | .fin₁ S => fun _ ↦ Term.pretty (.var "fin₁") 300 ++ .paren (Term.pretty S 0)
    | .id A => λ _ => Term.pretty (.var "id") 300 ++ .paren (Term.pretty A 0)
    | .image R X => fun _ ↦ Term.pretty R 300 ++ .sbracket (Term.pretty X 0)
    | .card S => λ _ => "‖" ++ Term.pretty S 0 ++ "‖"

  instance : ToString Term where
    toString t := toString (Term.pretty t 0)

  def reservedIdentifiers : Std.HashSet String :=
    {"MININT", "MAXINT", "NAT", "NAT1", "NATURAL", "NATURAL1", "INT", "INTEGER", "FLOAT", "REAL", "BOOL"}
end B.Syntax
