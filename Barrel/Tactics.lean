import Mathlib.Tactic.Core
import Mathlib.CategoryTheory.Category.Basic

namespace Barrel.Tactics
  register_label_attr wd_min
  register_label_attr wd_max
  register_label_attr wd_app
  register_label_attr wd_card

  register_label_attr pfun
  register_label_attr tfun

  syntax (name := pfun) "pfun" : tactic
  syntax (name := tfun) "tfun" : tactic

  set_option hygiene false in
  macro "pfun" : tactic => `(tactic| (
    intros
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | assumption
    | solve_by_elim using pfun, tfun))

  set_option hygiene false in
  macro "tfun" : tactic => `(tactic| (
    intros
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | assumption
    | solve_by_elim using tfun))

  syntax (name := wd_min) "wd_min" : tactic
  syntax (name := wd_max) "wd_max" : tactic
  syntax (name := wd_app) "wd_app" : tactic
  syntax (name := wd_card) "wd_card" : tactic

  set_option hygiene false in
  macro "wd_min" : tactic => `(tactic| (
    intros
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wd_min))

  set_option hygiene false in
  macro "wd_max" : tactic => `(tactic| (
    intros
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wd_max))

  set_option hygiene false in
  macro "wd_app" : tactic => `(tactic| (
    intros
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | (
        apply app.WD_of_mem_tfun
        · tfun
        · and_intros <;> grind
      )
    | (
        apply app.WD_of_mem_pfun
        · pfun
        · and_intros <;> grind
      )
    | solve_by_elim using wd_app))

  set_option hygiene false in
  macro "wd_card" : tactic => `(tactic| (
    intros
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wd_card))

  syntax (name := b_wd) "b_wd" : tactic
  macro "b_wd" : tactic => `(tactic| (
    subst_eqs
    generalize_proofs at *
    first | wd_min | wd_max | wd_app | wd_card
  ))

  syntax (name := b_typing) "b_typing" : tactic

  syntax (name := auto_solve) "barrel_solve" : tactic

  macro_rules | `(tactic| barrel_solve) => `(tactic| fail "`barrel_solve` failed to solve goal")
  -- macro_rules | `(tactic| barrel_solve) => `(tactic| grind)
  macro_rules | `(tactic| barrel_solve) => `(tactic| b_wd)
  macro_rules | `(tactic| barrel_solve) => `(tactic| b_typing)
  macro_rules | `(tactic| barrel_solve) => `(tactic| trivial)
  macro_rules | `(tactic| barrel_solve) => `(tactic| (repeat1 intro); barrel_solve)
end Barrel.Tactics
