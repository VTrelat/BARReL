import Barrel.Discharger
import Mathlib.Util.AssertNoSorry

-- set_option trace.barrel true
-- set_option trace.barrel.cache true
-- set_option trace.barrel.wf true
-- set_option trace.barrel.wf true
-- set_option trace.barrel.checkpoints true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

import machine JobQueue from "specs/"
prove_obligations_of JobQueue
-- next exact fun _ _ _ _ _ _ _ _ _ _ => card.WF_of_empty
next exact fun _ _ _ _ _ _ h _ => card.WF_of_finite h
next
  intros JOB _ _ deadline _ _ Ready_fin deadline_tfun _ Ready_nemp
  exact min.WF_of_finite_image_tfun deadline_tfun ⟨Ready_fin, Set.nonempty_iff_ne_empty.mpr Ready_nemp⟩
next
  intros JOB _ _ deadline _ _ Ready_fin deadline_tfun _ Ready_nemp _
  exact max.WF_of_finite_image_tfun deadline_tfun ⟨Ready_fin, Set.nonempty_iff_ne_empty.mpr Ready_nemp⟩
next exact fun JOB Limit MaxDeadline Ready deadline _ h h' _ _ _ _ _ _ _ =>
  JobQueue.Operation_enqueue_2.wf_0 JOB Limit Limit Ready deadline Limit h h'
next exact fun _ _ _ _ _ _ _ h _ _ _ _ _ h' _ _ => app.WF_of_mem_tfun h h'
next
  intros
  generalize_proofs at *
  apply card.WF_of_insert'
  assumption
next
  intros
  rw [Set.union_singleton]
  apply min.WF_of_finite_image_tfun <;> {
    first
    | assumption
    | apply FIN₁.of_insert <;> assumption
  }
next
  intros
  rw [Set.union_singleton]
  apply max.WF_of_finite_image_tfun <;> {
    first
    | assumption
    | apply FIN₁.of_insert <;> assumption
  }
next
  intros
  exact FIN.of_empty
next
  intros
  expose_names
  simpa only [card.of_empty] using Int.le_of_lt h.1
next
  intros
  expose_names
  rw [Set.union_singleton]
  exact FIN.of_insert h_7 h
next
  intros
  expose_names
  generalize_proofs at *
  simp
  rwa [card.of_insert _ ‹_›, ite_cond_eq_false _ _ (eq_false h_8)]
next
  intros
  expose_names
  simp only [Set.union_singleton]
  generalize_proofs card_wf min_wf max_wf app_wf min_wf_insert at *
  obtain ⟨_, _⟩ : B.Builtins.min (deadline[insert j Ready]) min_wf_insert ∈ NAT₁ := by
    have : deadline[insert j Ready] ⊆ NAT₁ := by
      intro x hx
      simp only [SetRel.mem_image] at hx
      obtain ⟨j', _, hj⟩ := hx
      exact h_1.1.1 hj |>.2
    exact this (min.mem min_wf_insert)
  assumption
next
  intros
  expose_names
  simp only [Set.union_singleton]
  generalize_proofs _ min_wf max_wf max_wf_insert at *

  have app_wf_j : app.WF deadline j := app.WF_of_mem_tfun h_1 h_7
  have : deadline[insert j Ready] = insert (deadline(j)'app_wf_j) (deadline[Ready]) := by
    simp only [SetRel.image_insert, B.Builtins.app.image_singleton_eq_of_wf app_wf_j,
      Set.singleton_union]
  simp [this]
  by_cases Ready_nemp : Ready.Nonempty
  · specialize min_wf (Set.nonempty_iff_ne_empty.mp Ready_nemp)
    specialize h_3 (Set.nonempty_iff_ne_empty.mp Ready_nemp)
    obtain ⟨min_ge_one, max_le_maxDeadline⟩ := h_3

    have max_wf : max.WF (deadline[Ready]) :=
      max_wf (Set.nonempty_iff_ne_empty.mp Ready_nemp) min_ge_one

    rw [max.of_insert _ max_wf]
    split_ifs with deadline_j_le_max
    · exact h_10
    · exact max_le_maxDeadline
  · rw [Set.not_nonempty_iff_eq_empty] at Ready_nemp
    subst Ready
    simpa

-- set_option trace.barrel.solve true
import refinement mm2 from "/Users/vtrelat/Documents/phd-b2smt/B/Mery"
prove_obligations_of mm2
