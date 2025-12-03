import Barrel.Discharger
import Mathlib.Util.AssertNoSorry

-- set_option trace.barrel.pog true
-- set_option trace.barrel.checkpoints true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- mch_discharger "specs/MinZ.mch"
-- next
--   admit
-- next
--   ext x
--   simp
--   exists {x}
--   exact Eq.symm min.of_singleton

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

mch_discharger "specs/Eval.mch"
next admit

mch_discharger "specs/Finite.mch"
next admit

mch_discharger "specs/Nat.mch"
next admit

mch_discharger "specs/Collect.mch"
next admit

mch_discharger "specs/Forall.mch"
next admit

mch_discharger "specs/Exists.mch"
next admit

-- -- -- TODO: fix
mch_discharger "specs/Injective.mch"
next
  intros X Y F x y F_inj _ _ x_mem_X y_mem_X
  admit
next
  intros X Y F x y F_inj _ _ x_mem_X y_mem_X
  admit
next
  rintro X Y F x y F_inj _ _ x_mem_X y_mem_X F_eq
  admit

-- -- -- TODO: fix
mch_discharger "specs/HO.mch"
next
  intros X Y x y₀ y₁ F x_mem_X y₀_mem_Y y₁_mem_Y y₀_neq_y₁ F_fun _ _ G G_fun
  admit
next
  intros X Y x y₀ y₁ F x_mem_X y₀_mem_Y y₁_mem_Y y₀_neq_y₁ F_fun _ _ G G_fun
  admit
next
  intros X Y x y₀ y₁ F x_mem_X y₀_mem_Y y₁_mem_Y y₀_neq_y₁ F_fun _ _

  by_cases hF : (x, y₀) ∈ F
  · exists F <+ {(x, y₁)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₁} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · admit
      -- exists wf_Fx', wf_Fx
      -- simpa [app.of_pair_eq wf_Fx hF, ne_comm] using y₀_neq_y₁
  · exists F <+ {(x, y₀)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₀} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · admit
      -- exists wf_Fx', wf_Fx
      -- simp
      -- intro contr
      -- rw [eq_comm, ←app.of_pair_iff] at contr
      -- contradiction

mch_discharger "specs/Demo.mch"
next
  exact fun _ => id
next
  intro s₀ hs₀
  apply FIN.of_inter
  left
  exact FIN.of_sub NAT.mem_FIN hs₀

-- -- -- TODO: fix
mch_discharger "specs/Extensionality.mch"
next
  intros X Y F G _ _ F_fun G_fun x hx
  exact app.WF_of_mem_tfun F_fun hx
next
  intros X Y F G _ _ F_fun G_fun x hx
  exact app.WF_of_mem_tfun G_fun hx
next
  intros X Y F G _ _ F_fun G_fun ext
  ext ⟨x, y⟩

  specialize ext x
  constructor <;> intro h
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq F_fun]
      exact mem_dom_of_pair_mem h

    -- rw [ext _ hx]
    -- exact app.pair_app_mem
    admit
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq G_fun]
      exact mem_dom_of_pair_mem h

    -- rw [←ext hx wf_F wf_G]
    -- exact app.pair_app_mem
    admit

mch_discharger "specs/CounterMin.mch"
next
  exact fun _ _ ↦ max.WF_singleton
next
  exact fun _ _ ↦ min.WF_singleton
next
  exact fun _ _ ↦ max.WF_of_finite
next
  exact fun _ _ ↦ min.WF_of_finite
next
  exact CounterMin.Operation_inc_2.wf_0
next
  exact CounterMin.Operation_inc_2.wf_1
next
  rintro _ z - - z_mem
  exact max.WF_interval <| neg_le_self z_mem
next
  rintro _ z - - z_mem
  exact min.WF_interval <| neg_le_self z_mem
next
  exact FIN₁.singleton_mem trivial
next
  intros _ _
  rw [max.of_singleton, min.of_singleton]
  rfl
next
  rintro X z - - z_mem
  exact interval.FIN₁_mem <| neg_le_self z_mem
next
  rintro X z - - hz
  rw [interval.min_eq (neg_le_self hz),
      interval.max_eq (neg_le_self hz),
      Int.neg_neg]

#check CounterMin.Initialisation_0
#check CounterMin.Initialisation_1
#check CounterMin.Operation_inc_2
#check CounterMin.Operation_inc_3

assert_no_sorry CounterMin.Initialisation_0
assert_no_sorry CounterMin.Initialisation_1
assert_no_sorry CounterMin.Operation_inc_2
assert_no_sorry CounterMin.Operation_inc_3
