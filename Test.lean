import B4Lean.Discharger

set_option trace.barrel.pog true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

mch_discharger "specs/Counter.mch"
next admit
next admit
next admit
next admit
-- next
--   grind
-- next
--   grind
-- next
--   rintro x ⟨_, _⟩ _ _
--   grind
-- next
--   grind

mch_discharger "specs/Eval.mch"
next admit

mch_discharger "specs/Finite.mch"
next admit

mch_discharger "specs/Nat.mch"
next admit
-- next
--   grind

mch_discharger "specs/Collect.mch"
next admit
-- next
--   grind

mch_discharger "specs/Forall.mch"
next admit
-- next
--   grind

mch_discharger "specs/Exists.mch"
next admit
-- next
--   exists 0

-- TODO: fix
mch_discharger "specs/Injective.mch"
next
  intros X y Y x F F_inj _ _ x_mem_X y_mem_X
  admit
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
mch_discharger "specs/HO.mch"
next
  intros X Y y0 y1 x F x_mem_X y0_mem_Y y1_mem_Y y0_neq_y1 F_fun _ _
  admit
-- next
--   admit

mch_discharger "specs/Enum.mch"
next admit
-- next
--   grind

mch_discharger "specs/Min.mch"
next
  intros X X_sub_INT
  admit
-- next admit
-- next
--   and_intros <;> grind

mch_discharger "specs/Union.mch"
next admit

mch_discharger "specs/Lambda.mch"
next admit

mch_discharger "specs/Demo.mch"
next admit
next admit

mch_discharger "specs/Test.mch"
next
  intros _ _
  admit


-- #check Counter.Initialisation_0
-- #check Counter.Initialisation_1
-- #check Counter.Operation_inc_2
-- #check Counter.Operation_inc_3
-- #check Nat.Initialisation_0
