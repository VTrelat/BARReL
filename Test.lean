import B4Lean.Discharger

set_option trace.barrel.pog false
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
  obtain ⟨⟨-, inj⟩, ⟨-,F_istot⟩⟩ := F_inj
  have Fx_WF : appWF F x := by
    simp [appWF, dom]
    obtain ⟨y, _, _⟩ := F_istot _ x_mem_X
    exists y
  have Fy_WF : appWF F y := by
    simp [appWF, dom]
    obtain ⟨y, _, _⟩ := F_istot _ y_mem_X
    exists y
  apply @inj x y (F(x)_@2)
  · unfold app
    rw [dite_cond_eq_true (eq_true Fx_WF)]
    generalize_proofs chs_Fx
    exact Classical.choose_spec chs_Fx
  · rw [F_eq]
    unfold app
    rw [dite_cond_eq_true (eq_true Fy_WF)]
    generalize_proofs chs_Fy
    exact Classical.choose_spec chs_Fy

-- mch_discharger "specs/HO.mch"
-- next
--   rintro X Y y₁ y₂ x F x_mem_X y₁_mem_Y y₂_mem_Y y₁_neq_y₂ F_fun - -
--   by_cases (F(x)_@3) = y₁
--   ·
--     admit
--   ·
--     admit

-- mch_discharger "specs/Enum.mch"
-- next
--   grind

mch_discharger "specs/Min.mch"
next
  unfold B.Builtins.min

  iterate 2 rw [dite_cond_eq_true]
  generalize_proofs h h'
  have hh := Classical.choose_spec h
  have hh' := Classical.choose_spec h'
  set m := Classical.choose h
  set m' := Classical.choose h'

  · admit
  · admit
  · unfold minWF
    done
