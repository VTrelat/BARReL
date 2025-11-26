import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import B.Syntax.Extra

namespace B.Builtins

abbrev NAT : Set ℤ := { n | 0 ≤ n ∧ n ≤ B.MAXINT }
abbrev NAT1 : Set ℤ := { n | 1 ≤ n ∧ n ≤ B.MAXINT }
abbrev NATURAL : Set ℤ := { n | 0 ≤ n }
abbrev NATURAL1 : Set ℤ := { n | 1 ≤ n }

abbrev INT : Set ℤ := { n | MININT ≤ n ∧ n ≤ MAXINT }

abbrev FLOAT : Set Float := Set.univ

abbrev REAL : Set ℝ := Set.univ

def interval (lo hi : ℤ) : Set ℤ := { n | lo ≤ n ∧ n ≤ hi }

infix:50 ".." => interval


end Builtins

end B
