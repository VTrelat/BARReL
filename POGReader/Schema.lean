import Std.Data.DHashMap
import Std.Data.HashMap
import B.Syntax

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
