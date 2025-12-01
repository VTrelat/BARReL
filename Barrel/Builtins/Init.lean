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
