import Std.Data.DHashMap
import Std.Data.HashMap

namespace B.Syntax
  inductive Typ : Type _
    | int | bool | real
    | pow : Typ → Typ
    | prod : Typ → Typ → Typ
    deriving DecidableEq, Inhabited, Repr

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
    | ℤ
    | 𝔹
    -- set operations
    | set (xs : Array Term)
    | mem (x : Term) (S : Term)
    | collect (vs : Array (String × Typ)) (D P : Term)
    | pow (S : Term)
    | cprod (S T : Term)
    | union (S T : Term)
    | inter (S T : Term)
    | card (S : Term)
    -- functions
    | app (f x : Term)
    | lambda (vs : Array (String × Typ)) (D P : Term)
    | pfun (A B : Term)
    -- | tfun (A B : Term)
    | min (S : Term) -- could be extended to minᵢ, minᵣ, etc.
    | max (S : Term)
    -- quantifiers
    | all (vs : Array (String × Typ)) (D P : Term)
    | exists (vs : Array (String × Typ)) (D P : Term)
    deriving Inhabited, Repr
end B.Syntax

namespace B.POG.Schema
  open B.Syntax

  structure Set : Type _ where
    name : String
    values : Array String
  deriving Repr

  inductive DefineType : Type _
    | ctx | seext | inv | ass
    | lprp | inprp | inext | cst | sets | mchcst
    | aprp | abs | imlprp | imprp | imext
    deriving BEq, Hashable, Repr

  inductive Define : DefineType → Type _
    | ctx : Array Set → Array Term → Define .ctx
    | seext : Array Term → Define .seext
    | inv : Array Term → Define .inv
    | ass : Array Term → Define .ass
    | lprp : Array Set → Array Term → Define .lprp
    | inprp : Array Set → Array Term → Define .inprp
    | inext : Array Term → Define .inext
    | cst : Array Term → Define .cst
    | sets : Array Set → Define .sets
    | mchcst : Array Term → Define .mchcst
    | aprp : Array Set → Array Term → Define .aprp
    | abs : Array Term → Define .abs
    | imlprp : Array Set → Array Term → Define .imlprp
    | imprp : Array Set → Array Term → Define .imprp
    | imext : Array Term → Define .imext
  deriving Repr

  structure SimpleGoal : Type _ where
    name : String
    refHyps : Array Nat
    goal : Term
  deriving Repr

  structure ProofObligation : Type _ where
    name : String
    uses : Array DefineType
    hypotheses : Array Term
    localHyps : Std.HashMap Nat Term
    simpleGoals : Array SimpleGoal
  deriving Repr

  instance : EmptyCollection ProofObligation where
    emptyCollection := ⟨"", ∅, ∅, ∅, ∅⟩

  structure ProofObligations : Type _ where
    defines : Std.DHashMap DefineType Define
    obligations : Array ProofObligation
    vars : Array (String × Syntax.Typ)
    -- typeInfos : Std.HashMap Nat Typ
  deriving Repr
end B.POG.Schema
