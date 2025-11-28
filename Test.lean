import B4Lean.Discharger

set_option trace.barrel.pog true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- mch_discharger "specs/Counter.mch"
-- next
--   grind
-- next
--   grind
-- next
--   rintro x ⟨_, _⟩ _ _
--   grind
-- next
--   grind

-- mch_discharger "specs/Nat.mch"
-- next
--   grind

-- mch_discharger "specs/Collect.mch"
-- next
--   grind

-- mch_discharger "specs/Forall.mch"
-- next
--   grind

-- mch_discharger "specs/Exists.mch"
-- next
--   exists 0

mch_discharger "specs/Injective.mch"
next
  rintro X y Y x F F_inj - - x_mem_X y_mem_X F_eq
  obtain ⟨⟨_, inj⟩, _⟩ := F_inj
  apply @inj x y (F(x))
  ·
    admit
  · rw [F_eq]
    admit

-- mch_discharger "specs/HO.mch"
-- next
--   rintro X Y y₁ y₂ x F x_mem_X y₁_mem_Y y₂_mem_Y y₁_neq_y₂ F_fun - -
--   by_cases (F(x)) = y₁
--   ·
--     admit
--   ·
--     admit

-- mch_discharger "specs/Enum.mch"
-- next
--   grind

mch_discharger "specs/Min.mch"
next
  unfold B.Builtins.INTEGER B.Builtins.min
  split_ifs with h
  · obtain ⟨x, x_mem, x_lt⟩ := h
    admit
  · -- NOTE: unprovable, as wanted!!
    admit
