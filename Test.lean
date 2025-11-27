import B4Lean.Discharger

-- set_option trace.b4lean.pog true
set_option b4lean.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

mch_discharger "specs/Counter.mch"
next
  grind
next
  grind
next
  rintro x ⟨_, _⟩ _ _
  grind
next
  grind

mch_discharger "specs/Nat.mch"
next
  grind

mch_discharger "specs/Collect.mch"
next
  grind

mch_discharger "specs/Forall.mch"
next
  grind

mch_discharger "specs/Exists.mch"
next
  exists 0

mch_discharger "specs/Injective.mch"
next
  admit

mch_discharger "specs/HO.mch"
next
  intro X Y y₁ y₂ x F x_mem_X y₁_mem_Y y₂_mem_Y y₁_neq_y₂ F_fun _ _
  by_cases F(x) = y₁
  · -- G = F(x ↦ y₂)
    admit
  · -- G = F(x ↦ y₁)
    admit

mch_discharger "specs/Enum.mch"
next
  grind

mch_discharger "specs/Lambda.mch"
next
  and_intros <;> grind

-- #check Counter.Initialisation_0
-- #check Counter.Initialisation_1
-- #check Counter.Operation_inc_2
-- #check Counter.Operation_inc_3
-- #check Nat.Initialisation_0
