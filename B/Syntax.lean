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
    | num (n : Int) (t : Typ)
    | bool (b : Bool)
    -- pairs
    | maplet (x y : Term)
    -- arithmetic
    | add (x y : Term)
    | sub (x y : Term)
    | mul (x y : Term)
    | le (x y : Term)
    | lt (x y : Term)
    -- logic
    | and (x y : Term)
    | or (x y : Term)
    | imp (x y : Term)
    | not (x : Term)
    | eq (x y : Term)
    -- sets
    -- basic sets
    | 𝔹
    | ℤ
    | ℝ
    -- set operations
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
    -- functions
    | app (f x : Term)
    | lambda (vs : Array (String × Typ)) (D P : Term)
    | «fun» (A B : Term) (isPartial := true)
    | injfun (A B : Term) (isPartial := true)
    | min (S : Term) -- could be extended to minᵢ, minᵣ, etc.
    | max (S : Term)
    -- quantifiers
    | all (vs : Array (String × Typ)) (P : Term)
    | exists (vs : Array (String × Typ)) (P : Term)
    deriving Inhabited, Repr

  partial def Term.pretty : Term -> Nat -> Std.Format
  | .var v => λ _ => v
  | .num n _ => λ _ => toString n
  | .bool x => λ _ => toString x
  | .𝔹 => λ _ => "𝔹"
  | .ℤ => λ _ => "ℤ"
  | .ℝ => λ _ => "ℝ"
  | .imp x y => «infixl» Term.pretty 30 "⇒" x y -- /!\ see manrefb p.198
  | .or x y => «infixl» Term.pretty 40 "∨" x y
  | .and x y => «infixl» Term.pretty 40 "∧" x y
  | .eq x y => «infixl» Term.pretty 60 "=" x y
  | .mem x S => «infixl» Term.pretty 120 "∈" x S
  | .subset S T => «infixl» Term.pretty 110 "⊆" S T
  | .rel A B => «infixl» Term.pretty 125 "↔" A B
  | .fun A B isPartial => «infixl» Term.pretty 125 (if isPartial then "⇸" else "⟶") A B
  | .injfun A B isPartial => «infixl» Term.pretty 125 (if isPartial then "⤔" else "↣") A B
  | .le x y => «infixl» Term.pretty 160 "≤" x y
  | .lt x y => «infixl» Term.pretty 160 "<" x y
  | .inter x y => «infixl» Term.pretty 160 "∩" x y
  | .union x y => «infixl» Term.pretty 160 "∪" x y
  | .maplet x y => «infixl» Term.pretty 160 "↦" x y
  | .add x y => «infixl» Term.pretty 180 "+" x y
  | .sub x y => «infixl» Term.pretty 180 "-" x y
  | .mul x y => «infixl» Term.pretty 190 "*" x y
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
    let vs' := "(" ++ ((v.map fun ⟨n, _⟩ ↦ n).toList |> String.intercalate ", ") ++ ")"
    binder Term.pretty 0 "λ " vs s!", {vs'} ∈ " D " ⇒ " P ""
  | .app f x => λ _ => Term.pretty f 300 ++ .paren (Term.pretty x 0)
  | .pow S => «prefix» Term.pretty 250 "𝒫 " S
  | .pow₁ S => «prefix» Term.pretty 250 "𝒫₁ " S
  | .min S => «prefix» Term.pretty 250 "min " S
  | .max S => «prefix» Term.pretty 250 "max " S
  | .card S => λ _ => "‖" ++ Term.pretty S 0 ++ "‖"

  instance : ToString Term where
    toString t := toString (Term.pretty t 0)

  def reservedIdentifiers : Std.HashSet String :=
    {"NAT", "NAT1", "NATURAL", "NATURAL1", "INT", "INTEGER", "FLOAT", "REAL", "BOOL"}
end B.Syntax
