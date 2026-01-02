import Barrel
import Mathlib.Util.AssertNoSorry

-- set_option trace.barrel true
-- set_option trace.barrel.cache true
-- set_option trace.barrel.wd true
-- set_option trace.barrel.checkpoints true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

set_option barrel.show_auto_solved true

import machine Counter from "specs/"
prove_obligations_of Counter
next grind

import machine Eval from "specs/"
prove_obligations_of Eval
next
  intros X Y _ _
  exists ∅, ∅, ∅
  exists ?_, ?_ <;> simp

import machine Finite from "specs/"
prove_obligations_of Finite
next
  grind
-- next
--   intros
--   exact interval.FIN_mem

import machine Nat from "specs/"
prove_obligations_of Nat
next
  grind
-- next
--   rintro _ ⟨_, _⟩
--   assumption

import machine Collect from "specs/"
prove_obligations_of Collect
next
  grind
-- next
--   simp

import machine Forall from "specs/"
prove_obligations_of Forall
next
  grind
-- next
--   rintro x1 x2 x3 ⟨⟨_, _⟩, _⟩ _
--   assumption

import machine Exists from "specs/"
prove_obligations_of Exists
next
  exists 0

import machine Injective from "specs/"
prove_obligations_of Injective
-- next
--   rintro X Y F x y _ _ ⟨_, F_tot⟩ x_mem_X _
--   exact app.WD_of_mem_tfun F_tot x_mem_X
-- next
--   rintro X Y F x y _ _ ⟨_, F_tot⟩ _ y_mem_X
--   exact app.WD_of_mem_tfun F_tot y_mem_X
next
  rintro X Y F x y _ _ ⟨⟨_, F_inj⟩, F_tot⟩ x_mem_X y_mem_X F_eq
  generalize_proofs wd_x wd_y at F_eq
  apply F_inj
  · exact app.pair_app_mem (wd := wd_x)
  · rw [F_eq]
    exact app.pair_app_mem (wd := wd_y)


import machine HO from "specs/"
prove_obligations_of HO
-- next
--   intros X Y x _ _ _ _ _ x_mem_X _ _ _ _ G G_fun
--   exact app.WD_of_mem_tfun G_fun x_mem_X
-- next
--   intros X Y x _ _ F _ _ x_mem_X _ _ _ F_fun _ _
--   exact app.WD_of_mem_tfun F_fun x_mem_X
next
  intros X Y x y₀ y₁ F _ _ x_mem_X y₀_mem_Y y₁_mem_Y y₀_neq_y₁ F_fun

  by_cases hF : (x, y₀) ∈ F
  · exists F <+ {(x, y₁)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₁} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · generalize_proofs _ wd_x
      rw [app.of_pair_iff wd_x] at hF
      simpa [hF, ←ne_eq, ne_comm, ne_eq]
  · exists F <+ {(x, y₀)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₀} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · generalize_proofs _ wd_x
      rw [app.of_pair_iff wd_x, ←ne_eq, ne_comm, ne_eq] at hF
      simpa

import machine Demo from "specs/"
prove_obligations_of Demo
-- next
--   exact fun _ => id
next
  intro s₀ hs₀
  apply FIN.of_inter
  left
  exact FIN.of_sub NAT.mem_FIN hs₀

import machine Extensionality from "specs/"
prove_obligations_of Extensionality
-- next
--   intros X Y F _ _ _ F_fun _ x hx
--   exact app.WD_of_mem_tfun F_fun hx
-- next
--   intros X Y _ G _ _ _ G_fun x hx
--   exact app.WD_of_mem_tfun G_fun hx
next
  intros X Y F G _ _ F_fun G_fun ext
  ext ⟨x, y⟩

  specialize ext x
  constructor <;> intro h
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq F_fun]
      exact mem_dom_of_pair_mem h

    specialize ext hx
    generalize_proofs wd_F wd_G at ext
    rw [app.of_pair_iff ‹_›] at h ⊢
    symm
    rwa [h] at ext
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq G_fun]
      exact mem_dom_of_pair_mem h
    specialize ext hx
    generalize_proofs wd_F wd_G at ext
    rw [app.of_pair_iff ‹_›] at h ⊢
    rwa [h] at ext

import machine CounterMin from "specs/"

prove_obligations_of CounterMin
next grind
next grind
next grind
next
  intros _ _
  rw [max.of_singleton, min.of_singleton]
  rfl
next grind
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

-- import machine Pixels from "specs/"
-- prove_obligations_of Pixels
-- next
--   rintro Colors Red Green Blue
--     pixels pixel pp hpixel rfl rfl Colors_card hpp color _ h₂
--   exact app.WD_of_mem_tfun hpp h₂
-- next
--   rintro Colors Red Green Blue _ rfl rfl Colors_card
--   and_intros
--   · rintro x (rfl|rfl|rfl) <;> simp
--   · intros x y z hxy hxz
--     simp at hxy hxz
--     obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hxy <;> {
--       obtain ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ := hxz
--       <;> rfl
--     }
--   · rintro x (rfl | rfl | rfl) <;> {
--       exists 0
--       simp
--     }
-- next
--   admit
-- next
--   simp_intro .. [*]
--   -- grind
--   admit
-- next
--   simp_intro .. [*]
--   -- grind
--   admit

import machine Collect2 from "specs/"
prove_obligations_of Collect2
next
  grind

import machine Lambda from "specs/"
prove_obligations_of Lambda
next
  and_intros
  · rintro ⟨⟨a, b⟩, c⟩ ⟨⟨_, _⟩, rfl⟩
    grind
  · rintro ⟨a, b⟩ c d ⟨⟨_, _⟩, rfl⟩ ⟨⟨_, _⟩, rfl⟩
    rfl
  · rintro ⟨x, y⟩ h
    obtain ⟨x_mem, y_mem⟩ := Set.prodMk_mem_set_prod_eq.mp h
    refine ⟨x + y, ?_, ⟨x_mem, y_mem⟩, rfl⟩
    grind

import machine Eta from "specs/"
prove_obligations_of Eta
-- next
--   intros X Y F _ _ F_tfun x _ x_mem
--   exact app.WD_of_mem_tfun F_tfun x_mem
next
  intros X Y F _ _ F_tfun
  ext ⟨x, y⟩
  dsimp
  generalize_proofs wd₁
  constructor
  · rintro ⟨_, h⟩
    rwa [eq_comm, ← app.of_pair_iff] at h
  · intro h

    have x_mem_dom : x ∈ X := by
      rw [← tfun_dom_eq F_tfun]
      apply mem_dom_of_pair_mem h

    constructor
    · rwa [app.of_pair_iff (wd₁ x_mem_dom), eq_comm] at h
    · assumption

import machine DerivFalse from "examples/"

prove_obligations_of DerivFalse
next
  exists B.Builtins.min ∅ ?_
  · -- unprovable
    admit
  · refine ⟨?_, ?_⟩
    · exact trivial
    · intro
      generalize_proofs wd at *
      obtain ⟨_, contr, _⟩ := wd
      contradiction
