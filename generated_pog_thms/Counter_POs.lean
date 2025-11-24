/-
Auto-generated from `specs/Counter.mch`.
Source POG: `/var/folders/pp/xq1kl97d1nggh40s9c6g97hw0000gn/T/tmp.eqjDmDVt/tmp.pog`.
-/

import Mathlib.Data.Set.Basic
variable (x : Int)

-- Initialisation POs
section Initialisation_POs

/--
Proof obligation `Initialisation` goal 1/2, goal tag `Invariant is preserved`.
  - defs: none
  - hyps: none
  - goal: 0 ∈ᴮ { x1 ∈ᴮ ℤ | 0 ≤ᴮ x1 ∧ᴮ x1 ≤ᴮ 2147483647 }
-/
theorem Initialisation_1 : 0 ∈ { x1 : Int | x1 ∈ Set.univ → 0 ≤ x1 ∧ x1 ≤ 2147483647 } := by
  sorry

/--
Proof obligation `Initialisation` goal 2/2, goal tag `Invariant is preserved`.
  - defs: none
  - hyps: none
  - goal: 0 ≤ᴮ 10
-/
theorem Initialisation_2 : 0 ≤ 10 := by
  sorry

end Initialisation_POs

-- InvariantPreservation POs
section InvariantPreservation_POs

/--
Proof obligation `Operation_inc` goal 1/2, goal tag `Invariant is preserved`.
  - defs: x ∈ᴮ { x0 ∈ᴮ ℤ | 0 ≤ᴮ x0 ∧ᴮ x0 ≤ᴮ 2147483647 }
  - defs: x ≤ᴮ 10
  - hyps: ¬ᴮ(10 ≤ᴮ x)
  - goal: x +ᴮ 1 ∈ᴮ { x2 ∈ᴮ ℤ | 0 ≤ᴮ x2 ∧ᴮ x2 ≤ᴮ 2147483647 }
-/
theorem Operation_inc_1 : (x ∈ { x0 : Int | x0 ∈ Set.univ → 0 ≤ x0 ∧ x0 ≤ 2147483647 }) → (x ≤ 10) → (¬ (10 ≤ x)) → x + 1 ∈ { x2 : Int | x2 ∈ Set.univ → 0 ≤ x2 ∧ x2 ≤ 2147483647 } := by
  sorry

/--
Proof obligation `Operation_inc` goal 2/2, goal tag `Invariant is preserved`.
  - defs: x ∈ᴮ { x0 ∈ᴮ ℤ | 0 ≤ᴮ x0 ∧ᴮ x0 ≤ᴮ 2147483647 }
  - defs: x ≤ᴮ 10
  - hyps: ¬ᴮ(10 ≤ᴮ x)
  - goal: x +ᴮ 1 ≤ᴮ 10
-/
theorem Operation_inc_2 : (x ∈ { x0 : Int | x0 ∈ Set.univ → 0 ≤ x0 ∧ x0 ≤ 2147483647 }) → (x ≤ 10) → (¬ (10 ≤ x)) → x + 1 ≤ 10 := by
  sorry

end InvariantPreservation_POs
