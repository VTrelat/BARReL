/-
Auto-generated from `specs/Demo.mch`.
Source POG: `/var/folders/pp/xq1kl97d1nggh40s9c6g97hw0000gn/T/tmp.RwtLZOPf/tmp.pog`.
-/

import Mathlib.Data.Set.Basic
variable (s0 : Set (Int))

-- Initialisation POs
section Initialisation_POs

/--
Proof obligation `Initialisation` goal 1/2, goal tag `Invariant is preserved`.
  - defs: none
  - hyps: s0 ∈ᴮ 𝒫 ({ x15 ∈ᴮ ℤ | 0 ≤ᴮ x15 ∧ᴮ x15 ≤ᴮ 2147483647 })
  - goal: ∀ᴮ x18 ∈ᴮ s0. x18 ∈ᴮ { x16 ∈ᴮ ℤ | 0 ≤ᴮ x16 ∧ᴮ x16 ≤ᴮ 2147483647 }
-/
theorem Initialisation_1 : (s0 ∈ 𝒫 ({ x15 : Int | x15 ∈ Set.univ → 0 ≤ x15 ∧ x15 ≤ 2147483647 })) → ∀ x18 : Int, x18 ∈ s0 → x18 ∈ { x16 : Int | x16 ∈ Set.univ → 0 ≤ x16 ∧ x16 ≤ 2147483647 } := by
  sorry

/--
Proof obligation `Initialisation` goal 2/2, goal tag `Invariant is preserved`.
  - defs: none
  - hyps: s0 ∈ᴮ 𝒫 ({ x15 ∈ᴮ ℤ | 0 ≤ᴮ x15 ∧ᴮ x15 ≤ᴮ 2147483647 })
  - goal: s0 ∩ᴮ { x21 ∈ᴮ ℤ | ¬ᴮ(x21 ∈ᴮ { x19 ∈ᴮ ℤ | 0 ≤ᴮ x19 }) } ∈ᴮ { x22 ∈ᴮ 𝒫 ℤ | ∃ᴮ x23 ∈ᴮ ℤ. ∃ᴮ x24 ∈ᴮ x22 ⇸ᴮ ℤ. (∀ᴮ x27 ∈ᴮ x22. ∀ᴮ x28 ∈ᴮ x22. x24(x27) =ᴮ x24(x28) ⇒ᴮ x27 =ᴮ x28) ∧ᴮ (x22 =ᴮ { x29 ∈ᴮ ℤ | ∃ᴮ x30 ∈ᴮ ℤ. x29 ↦ᴮ x30 ∈ᴮ x24 }) ∧ᴮ (∀ᴮ x25,x26 ∈ᴮ x22 ⨯ᴮ ℤ. x25 ↦ᴮ x26 ∈ᴮ x24 ⇒ᴮ 0 ≤ᴮ x26 ∧ᴮ x26 ≤ᴮ x23) }
-/
theorem Initialisation_2 : (s0 ∈ 𝒫 ({ x15 : Int | x15 ∈ Set.univ → 0 ≤ x15 ∧ x15 ≤ 2147483647 })) → s0 ∩ { x21 : Int | x21 ∈ Set.univ → ¬ (x21 ∈ { x19 : Int | x19 ∈ Set.univ → 0 ≤ x19 }) } ∈ { x22 : Set (Int) | x22 ∈ 𝒫 Set.univ → ∃ x23 : Int, x23 ∈ Set.univ ∧ ∃ x24 : Int, x24 ∈ x22 ⇸ Set.univ ∧ ((∀ x27 : Int, x27 ∈ x22 → (∀ x28 : Int, x28 ∈ x22 → x24(x27) = x24(x28) → x27 = x28)) ∧ (x22 = { x29 : Int | x29 ∈ Set.univ → ∃ x30 : Int, x30 ∈ Set.univ ∧ x29 ↦ x30 ∈ x24 }) ∧ (∀ x25,x26 : Int, x25 ↦ x26 ∈ x22 ⨯ Set.univ → x25 ↦ x26 ∈ x24 → 0 ≤ x26 ∧ x26 ≤ x23)) } := by
  sorry

end Initialisation_POs
