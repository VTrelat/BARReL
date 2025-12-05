import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

namespace B.Builtins
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

end B.Builtins

------------------------------

/-
  A slightly nicer notation for conjunctions, instead of using `Exists`.
-/

abbrev DepAnd {P : Prop} (Q : P → Prop) : Prop := @Exists P Q

section
  open Lean -- TSyntax.Compat

  macro:35 "(" x:withoutPosition(binderIdent ppSpace) ": " a:term ")" " ∧' " b:term:35 : term => do
    match x with
    | `(binderIdent| _) => `(DepAnd fun (_ : $a) => $b)
    | `(binderIdent| $x:ident) => `(DepAnd fun ($x : $a) => $b)
    | _ => Macro.throwUnsupported
  macro:35 a:term:36 " ∧' " b:term:35 : term => `(DepAnd fun (_ : $a) => $b)

  @[app_unexpander DepAnd] meta def unexpandDepAnd : Lean.PrettyPrinter.Unexpander
    | `($_ fun ($x:ident : $t) => $b) => `(($x:ident : $t) ∧' $b)
    | `($_ fun (_ : $t) => $b) => `($t ∧' $b)
    -- | `($(_) fun $x:ident => $b) => `(($x:ident : _) ∧' $b)
    | _                                  => throw ()

  open PrettyPrinter Delaborator SubExpr
  def delabDepAndCore : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
    guard $ (← getExpr).getAppNumArgs == 2
    guard $ (← getExpr).appArg!.isLambda
    withAppArg do
      let α ← withBindingDomain delab
      let bodyExpr := (← getExpr).bindingBody!
      withBindingBodyUnusedName fun n => do
        let b ← delab
        if bodyExpr.hasLooseBVars then
          `(($(⟨n⟩):ident : $α) ∧' $b)
        else
          `($α ∧' $b)

  @[delab app.DepAnd]
  def delabSigma : Delab := delabDepAndCore
end
