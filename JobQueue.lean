import BARReL

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

set_option barrel.show_auto_solved true

open B.Builtins

import machine JobQueue from "specs/"

prove_obligations_of JobQueue
next
  intros
  expose_names
  exact min.WF_of_finite_image_tfun h_4 ⟨h_3, Set.nonempty_iff_ne_empty.mpr h_6⟩
next
  intros
  expose_names
  exact max.WF_of_finite_image_tfun h_4 ⟨h_3, Set.nonempty_iff_ne_empty.mpr h_6⟩
next exact fun JOB Limit MaxDeadline Ready deadline j h h_9 h_10 h_11 h_12 h_13 h_14 h_15 h_16 =>
  JobQueue.Operation_enqueue_2.wf_0 JOB Limit Limit Ready deadline Limit h h_9 h_9 h_11 h_12
next exact
  fun JOB Limit MaxDeadline Ready deadline j h h_10 h_11 h_12 h_13 h_14 h_15 h_16 h_17 h_18 =>
  app.WF_of_mem_tfun h_13 h_16
next barrel_solve
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
  simpa only [card.of_empty] using Int.le_of_lt h_1.1
next
  intros
  expose_names
  rw [Set.union_singleton]
  exact FIN.of_insert h_7 h_3
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
      exact h_4.1.1 hj |>.2
    exact this (min.mem min_wf_insert)
  assumption
next
  intros
  expose_names
  simp only [Set.union_singleton]
  generalize_proofs card_wf min_wf max_wf app_wf max_wf_insert at *

  have : deadline[insert j Ready] = insert (deadline(j)'app_wf) (deadline[Ready]) := by
    simp only [SetRel.image_insert, B.Builtins.app.image_singleton_eq_of_wf app_wf,
      Set.singleton_union]
  simp [this]
  by_cases Ready_nemp : Ready.Nonempty
  · specialize min_wf (Set.nonempty_iff_ne_empty.mp Ready_nemp)
    specialize h_6 (Set.nonempty_iff_ne_empty.mp Ready_nemp)
    obtain ⟨min_ge_one, max_le_maxDeadline⟩ := h_6

    have max_wf : max.WF (deadline[Ready]) :=
      max_wf (Set.nonempty_iff_ne_empty.mp Ready_nemp) min_ge_one

    rw [max.of_insert _ max_wf]
    split_ifs with deadline_j_le_max
    · exact h_10
    · exact max_le_maxDeadline
  · rw [Set.not_nonempty_iff_eq_empty] at Ready_nemp
    subst Ready
    simpa
