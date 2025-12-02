import Barrel.Discharger

set_option trace.barrel.pog false
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- set_option trace.barrel.pog true
-- mch_discharger "specs/Counter.mch"
-- next grind
-- next admit
-- next admit
-- next admit
-- next
--   grind
-- next
--   grind
-- next
--   rintro x ⟨_, _⟩ _ _
--   grind
-- next
--   grind

-- mch_discharger "specs/Eval.mch"
-- next admit

-- mch_discharger "specs/Finite.mch"
-- next admit

-- mch_discharger "specs/Nat.mch"
-- next admit
-- -- next
-- --   grind

-- mch_discharger "specs/Collect.mch"
-- next admit
-- -- next
-- --   grind

-- mch_discharger "specs/Forall.mch"
-- next admit
-- -- next
-- --   grind

-- mch_discharger "specs/Exists.mch"
-- next admit
-- -- next
-- --   exists 0

-- -- TODO: fix
-- mch_discharger "specs/Injective.mch"
-- next
--   intros X y Y x F F_inj _ _ x_mem_X y_mem_X
--   admit
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


mch_discharger "specs/HO.mch"
next
  intros X Y x y₀ y₁ F x_mem_X y₀_mem_Y y₁_mem_Y y₀_neq_y₁ F_fun _ _
  have wf_Fx : app.WF F x := app.WF_of_mem_tfun F_fun x_mem_X
  have wf_Fx' {z} : app.WF (F <+ {(x, z)}) x :=
    app.WF_of_overload F_fun.1 pfun_of_singleton (Or.inr ⟨z, rfl⟩)

  by_cases hF : (x, y₀) ∈ F
  · exists F <+ {(x, y₁)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₁} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · exists wf_Fx', wf_Fx
      simpa [app.of_pair_eq wf_Fx hF, ne_comm] using y₀_neq_y₁
  · exists F <+ {(x, y₀)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₀} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · exists wf_Fx', wf_Fx
      simp
      intro contr
      rw [eq_comm, ←app.of_pair_iff] at contr
      contradiction

mch_discharger "specs/Demo.mch"
next
  exact fun _ => id
next
  intro s₀ hs₀
  apply FIN.of_inter
  left
  exact FIN.of_sub NAT.mem_FIN hs₀


-- set_option trace.barrel.checkpoints true

mch_discharger "specs/Extensionality.mch"
next
  intros X Y F G _ _ F_fun G_fun ext
  ext ⟨x, y⟩

  specialize ext x
  constructor <;> intro h
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq F_fun]
      exact mem_dom_of_pair_mem h

    have wf_F : app.WF F x := app.WF_of_mem_tfun F_fun hx
    have wf_G : app.WF G x := app.WF_of_mem_tfun G_fun hx

    obtain rfl := (app.of_pair_eq wf_F h).symm

    rw [ext hx wf_F wf_G]
    exact app.pair_app_mem
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq G_fun]
      exact mem_dom_of_pair_mem h

    have wf_F : app.WF F x := app.WF_of_mem_tfun F_fun hx
    have wf_G : app.WF G x := app.WF_of_mem_tfun G_fun hx

    obtain rfl := (app.of_pair_eq wf_G h).symm

    rw [←ext hx wf_F wf_G]
    exact app.pair_app_mem

mch_discharger "specs/CounterMin.mch"
next
  exact FIN₁.singleton_mem trivial
next
  exists max.WF_singleton, min.WF_singleton
  simp
next
  rintro z X hX
  exists max.WF_of_finite hX, min.WF_of_finite hX
  rintro - hz
  exact interval.FIN₁_mem (neg_le_self hz)
next
  intro z X hX
  exists max.WF_of_finite hX, min.WF_of_finite hX
  rintro - hz
  exists
    max.WF_of_finite (interval.FIN₁_mem (neg_le_self hz)),
    min.WF_of_finite (interval.FIN₁_mem (neg_le_self hz))
  rw [interval.min_eq (neg_le_self hz),
      interval.max_eq (neg_le_self hz),
      Int.neg_neg]

#check CounterMin.Initialisation_0
#check CounterMin.Initialisation_1
#check CounterMin.Operation_inc_2
#check CounterMin.Operation_inc_3
