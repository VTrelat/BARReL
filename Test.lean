import Barrel
import Mathlib.Util.AssertNoSorry

-- set_option trace.barrel true
-- set_option trace.barrel.cache true
-- set_option trace.barrel.wd true
-- set_option trace.barrel.checkpoints true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- set_option barrel.show_auto_solved true

import machine Counter from "specs/"

qed Counter

import machine Eval from "specs/"
next obligation of Eval by
  intros X Y _ _
  exists ∅, ∅, ∅
  exists ?_, ?_ <;> simp

qed Eval

import machine Finite from "specs/"
-- next obligation of Finite by
--   intros
--   exact interval.FIN_mem

qed Finite

import machine Nat from "specs/"
-- next obligation of Nat by
--   rintro _ ⟨_, _⟩
--   assumption

qed Nat

import machine Collect from "specs/"
-- next obligation of Collect by
--   simp

qed Collect

import machine Forall from "specs/"
-- next obligation of Forall by
--   rintro x1 x2 x3 ⟨⟨_, _⟩, _⟩ _
--   assumption

qed Forall

import machine Exists from "specs/"
next obligation of Exists by
  exists 0

qed Exists

import machine Injective from "specs/"
-- next obligation of Injective by
--   rintro X Y F x y _ _ ⟨_, F_tot⟩ x_mem_X _
--   exact app.WD_of_mem_tfun F_tot x_mem_X
-- next obligation of Injective by
--   rintro X Y F x y _ _ ⟨_, F_tot⟩ _ y_mem_X
--   exact app.WD_of_mem_tfun F_tot y_mem_X
qed Injective

import machine HO from "specs/"
-- next obligation of HO by
--   intros X Y x _ _ _ _ _ x_mem_X _ _ _ _ G G_fun
--   exact app.WD_of_mem_tfun G_fun x_mem_X
-- next obligation of HO by
--   intros X Y x _ _ F _ _ x_mem_X _ _ _ F_fun _ _
--   exact app.WD_of_mem_tfun F_fun x_mem_X
next obligation of HO by
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

qed HO

import machine Demo from "specs/"
-- next obligation of Demo by
--   exact fun _ => id
obligation Initialisation_1 of Demo by
  intro s₀ hs₀
  apply FIN.of_inter
  left
  exact FIN.of_sub NAT.mem_FIN hs₀

qed Demo

import machine Extensionality from "specs/"
-- next obligation of Extensionality by
--   intros X Y F _ _ _ F_fun _ x hx
--   exact app.WD_of_mem_tfun F_fun hx
-- next obligation of Extensionality by
--   intros X Y _ G _ _ _ G_fun x hx
--   exact app.WD_of_mem_tfun G_fun hx
qed Extensionality

import machine CounterMin from "specs/"

qed CounterMin

#check CounterMin.Initialisation_0
#check CounterMin.Initialisation_1
#check CounterMin.Operation_inc_2
#check CounterMin.Operation_inc_3

assert_no_sorry CounterMin.Initialisation_0
assert_no_sorry CounterMin.Initialisation_1
assert_no_sorry CounterMin.Operation_inc_2
assert_no_sorry CounterMin.Operation_inc_3

-- import machine Pixels from "specs/"
-- next obligation of Pixels by
--   rintro Colors Red Green Blue
--     pixels pixel pp hpixel rfl rfl Colors_card hpp color _ h₂
--   exact app.WD_of_mem_tfun hpp h₂
-- next obligation of Pixels by
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
-- next obligation of Pixels by
--   admit
-- next obligation of Pixels by
--   simp_intro .. [*]
--   -- grind
--   admit
-- next obligation of Pixels by
--   simp_intro .. [*]
--   -- grind
--   admit

-- qed Pixels

import machine Collect2 from "specs/"

qed Collect2

import machine Lambda from "specs/"
next obligation of Lambda by
  and_intros
  · rintro ⟨⟨a, b⟩, c⟩ ⟨⟨_, _⟩, rfl⟩
    grind
  · rintro ⟨a, b⟩ c d ⟨⟨_, _⟩, rfl⟩ ⟨⟨_, _⟩, rfl⟩
    rfl
  · rintro ⟨x, y⟩ h
    obtain ⟨x_mem, y_mem⟩ := Set.prodMk_mem_set_prod_eq.mp h
    refine ⟨x + y, ?_, ⟨x_mem, y_mem⟩, rfl⟩
    grind

qed Lambda

import machine Eta from "specs/"
-- next obligation of Eta by
--   intros X Y F _ _ F_tfun x _ x_mem
--   exact app.WD_of_mem_tfun F_tfun x_mem
next obligation of Eta by
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

qed Eta
