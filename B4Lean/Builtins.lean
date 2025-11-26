import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import B.Syntax.Extra

namespace B.Builtins

abbrev MAXINT : ℤ := B.MAXINT
abbrev MININT : ℤ := B.MININT

abbrev NAT : Set ℤ := { n | 0 ≤ n ∧ n ≤ MAXINT }
abbrev NAT1 : Set ℤ := { n | 1 ≤ n ∧ n ≤ MAXINT }
abbrev NATURAL : Set ℤ := { n | 0 ≤ n }
abbrev NATURAL1 : Set ℤ := { n | 1 ≤ n }

abbrev INT : Set ℤ := { n | MININT ≤ n ∧ n ≤ MAXINT }

abbrev FLOAT : Set Float := Set.univ

abbrev REAL : Set ℝ := Set.univ

def varIsReserved : String → Prop
  | "NAT" | "NAT1" | "NATURAL" | "NATURAL1"
  | "INT"
  | "FLOAT"
  | "REAL"
    => True
  | _ => False

instance : DecidablePred varIsReserved := by
  intro v
  unfold varIsReserved
  split <;>
  first
  | exact instDecidableTrue
  | exact instDecidableFalse

def interval (lo hi : ℤ) : Set ℤ := { n | lo ≤ n ∧ n ≤ hi }

infix:50 ".." => interval


end Builtins

open Lean Elab Builtins

def reservedVarToExpr : String → TermElabM Lean.Expr
  | "NAT" => return mkConst ``NAT
  | "NAT1" => return mkConst ``NAT1
  | "NATURAL" => return mkConst ``NATURAL
  | "NATURAL1" => return mkConst ``NATURAL1
  | "INT" => return mkConst ``INT
  | v => throwError "Variable {v} is not reserved."

end B
