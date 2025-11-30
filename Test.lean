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

-- mch_discharger "specs/Injective.mch"
-- next
--   rintro X y Y x F F_inj - - x_mem_X y_mem_X
--   refine ⟨?_, ?B, ?_⟩
--   ·
--     admit
--   ·
--     admit
--   · intro F_eq
--     obtain ⟨⟨_, inj⟩, _⟩ := F_inj
--     apply @inj x y (F(x)'?B)
--     ·
--       admit
--     · rw [F_eq]
--       admit

-- TODO: fix
-- mch_discharger "specs/HO.mch"
-- next
--   admit

-- mch_discharger "specs/Enum.mch"
-- next
--   grind

mch_discharger "specs/Min.mch"
next
  admit
-- next admit
-- next
--   and_intros <;> grind

-- pog_discharger "/Users/vtrelat/Documents/phd-b2smt/benchmark/"


-- #check Counter.Initialisation_0
-- #check Counter.Initialisation_1
-- #check Counter.Operation_inc_2
-- #check Counter.Operation_inc_3
-- #check Nat.Initialisation_0
