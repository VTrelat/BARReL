import Mathlib.Tactic.Core
import Mathlib.CategoryTheory.Category.Basic

namespace Barrel.Tactics
  register_label_attr wf_min
  register_label_attr wf_max
  register_label_attr wf_app
  register_label_attr wf_card

  syntax (name := wf_min) "wf_min" : tactic
  syntax (name := wf_max) "wf_max" : tactic
  syntax (name := wf_app) "wf_app" : tactic
  syntax (name := wf_card) "wf_card" : tactic

  set_option hygiene false in
  macro "wf_min" : tactic => `(tactic| (
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wf_min))

  set_option hygiene false in
  macro "wf_max" : tactic => `(tactic| (
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wf_max))

  set_option hygiene false in
  macro "wf_app" : tactic => `(tactic| (
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wf_app))

  set_option hygiene false in
  macro "wf_card" : tactic => `(tactic| (
    subst_eqs
    generalize_proofs at *
    first
    | sorry_if_sorry
    | solve_by_elim using wf_card))

  syntax (name := b_wf) "b_wf" : tactic
  macro "b_wf" : tactic => `(tactic| (
    subst_eqs
    generalize_proofs at *
    first | wf_min | wf_max | wf_app | wf_card
  ))

  syntax (name := b_typing) "b_typing" : tactic

  syntax (name := auto_solve) "barrel_solve" : tactic

  macro_rules | `(tactic| barrel_solve) => `(tactic| fail "`barrel_solve` failed to solve goal")
  -- macro_rules | `(tactic| barrel_solve) => `(tactic| grind)
  macro_rules | `(tactic| barrel_solve) => `(tactic| b_wf)
  macro_rules | `(tactic| barrel_solve) => `(tactic| b_typing)
  macro_rules | `(tactic| barrel_solve) => `(tactic| trivial)
  macro_rules | `(tactic| barrel_solve) => `(tactic| (repeat1 intro); barrel_solve)
end Barrel.Tactics
