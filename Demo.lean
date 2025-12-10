import Barrel.Discharger
import Mathlib.Util.AssertNoSorry

-- set_option trace.barrel true
-- set_option trace.barrel.cache true
-- set_option trace.barrel.wf true
-- set_option trace.barrel.checkpoints true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

mch_discharger "specs/JobQueue.mch"
next exact fun _ _ _ _ _ _ _ _ _ _ => card.WF_of_empty
next exact fun _ _ _ _ _ _ _ h _ => card.WF_of_finite h
next
  intros JOB _ _ Ready deadline _ _ Ready_fin deadline_tfun _ Ready_nemp
  exact min.WF_of_finite_image_tfun deadline_tfun ⟨Ready_fin, Set.nonempty_iff_ne_empty.mpr Ready_nemp⟩
next
  intros JOB _ _ Ready deadline _ _ Ready_fin deadline_tfun _ Ready_nemp _
  exact max.WF_of_finite_image_tfun deadline_tfun ⟨Ready_fin, Set.nonempty_iff_ne_empty.mpr Ready_nemp⟩
next exact fun _ Limit MaxDeadline _ _ j h h' h'' _ _ _ _ _ _ _ =>
  JobQueue.Operation_enqueue_2.wf_0 _ Limit MaxDeadline _ _ j h h' h''
next exact fun _ _ _ _ _ _ _ _ h _ _ _ _ _ h' _ _ => app.WF_of_mem_tfun h h'
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
next exact
  fun JOB Limit MaxDeadline Ready deadline j h h_10 h_11 h_12 _ _ _ _ _ h_18 =>
  app.WF_of_mem_tfun h_11 (h h_18)
next
  exact fun JOB Limit MaxDeadline Ready deadline j h h_1 h_2 h_3 _ _ _ _ _ h_9 =>
    min.WF_of_finite_image_tfun h_2 ⟨h_1, Set.nonempty_of_mem h_9⟩
next
  intros
  generalize_proofs at *
  apply card.WF_of_sdiff
  assumption
next
  intros
  expose_names
  apply min.WF_of_finite_image_tfun <;> try assumption
  exact ⟨FIN.of_sub h_1 Set.diff_subset, Set.nonempty_iff_ne_empty.mpr h_11⟩
next
  intros
  expose_names
  apply max.WF_of_finite_image_tfun <;> try assumption
  exact ⟨FIN.of_sub h_1 Set.diff_subset, Set.nonempty_iff_ne_empty.mpr h_11⟩
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
  rintro i (hi | rfl)
  · exact h hi
  · exact h_8
next
  intros
  expose_names
  rw [Set.union_singleton]
  exact FIN.of_insert h_8 h_1
next
  intros
  expose_names
  generalize_proofs at *
  simp
  rwa [card.of_insert _ ‹_›, ite_cond_eq_false _ _ (eq_false h_9)]
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
      exact h_2.1.1 hj |>.2
    exact this (min.mem min_wf_insert)
  assumption
next
  intros
  expose_names
  simp only [Set.union_singleton]
  generalize_proofs _ min_wf max_wf max_wf_insert at *

  have app_wf_j : app.WF deadline j := app.WF_of_mem_tfun h_2 h_8
  have : deadline[insert j Ready] = insert (deadline(j)'app_wf_j) (deadline[Ready]) := by
    simp only [SetRel.image_insert, B.Builtins.app.image_singleton_eq_of_wf app_wf_j,
      Set.singleton_union]
  simp [this]
  by_cases Ready_nemp : Ready.Nonempty
  · specialize min_wf (Set.nonempty_iff_ne_empty.mp Ready_nemp)
    specialize h_4 (Set.nonempty_iff_ne_empty.mp Ready_nemp)
    obtain ⟨min_ge_one, max_le_maxDeadline⟩ := h_4

    have max_wf : max.WF (deadline[Ready]) :=
      max_wf (Set.nonempty_iff_ne_empty.mp Ready_nemp) min_ge_one

    rw [max.of_insert _ max_wf]
    split_ifs with deadline_j_le_max
    · exact h_11
    · exact max_le_maxDeadline
  · rw [Set.not_nonempty_iff_eq_empty] at Ready_nemp
    subst Ready
    simpa
next
  intros
  expose_names
  simp
  trans JOB
  · assumption
  · exact Set.subset_insert j JOB
next
  intros
  expose_names
  exact FIN.of_sub (A := JOB) h_1 Set.diff_subset
next
  intros
  expose_names
  generalize_proofs at *
  rw [card.of_diff_singleton _ ‹_›, ite_cond_eq_true _ _ (eq_true h_9)]
  rw [tsub_le_iff_right]
  trans Limit
  · exact h_3
  · exact Int.le_add_one (Int.le_refl Limit)
next
  intros
  expose_names
  generalize_proofs at *
  suffices B.Builtins.min (deadline[Ready \ {j}]) ‹_› ∈ NAT₁ by
    exact this.1
  have := min.mem (S := deadline[Ready \ {j}]) ‹_›
  simp at this
  obtain ⟨_, _, this⟩ := this
  exact h_2.1.1 this |>.2
next
  intros
  expose_names
  obtain ⟨min_ge, max_le⟩ := h_4 h_8
  generalize_proofs at *
  trans B.Builtins.max (deadline[Ready]) ‹_›
  · apply max.mono
    intro z hz
    simp only [SetRel.mem_image, Set.mem_diff, Set.mem_singleton_iff] at hz
    obtain ⟨w, ⟨_, _⟩, _⟩ := hz
    exists w
  · exact max_le
