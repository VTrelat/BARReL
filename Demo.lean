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
next exact fun _ _ _ _ _ _ _ _ _ _ => card.WF_of_empty
next exact fun JOB Limit MaxDeadline Ready deadline j h h_3 h_4 h h_5 =>
  card.WF_of_finite h
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

set_option barrel.show_auto_solved true

import machine MinSearch from "specs/case_study"
import refinement MinSearch_r1 from "specs/case_study"
import refinement MinSearch_r2 from "specs/case_study"
-- import implementation MinSearch_i from "specs/case_study" -- Atelier-B crashes on this one ??

prove_obligations_of MinSearch
next
  intros
  exact min.WF_singleton
next
  intros
  exact min.WF_of_finite ‹_›
next
  intros
  apply min.WF_of_union <;> exact (min.WF_of_finite ‹_›)
next
  simp only [Set.sep_setOf, Set.subset_univ, true_and, Set.mem_setOf_eq,
    Set.singleton_subset_iff, Set.finite_singleton, and_true, Set.singleton_nonempty, imp_self,
    implies_true]
next
  intros
  rw [min.of_singleton]
next
  intros
  exact FIN₁.of_union ‹_› (FIN₁.mono Set.diff_subset ‹_›)
next
  introv
  have : done ∪ add ⊆ SS := by grind
  generalize_proofs min_wf
  exact this (min.mem min_wf)

prove_obligations_of MinSearch_r1
next exact fun SS done1 mm1 done mm xx mi mi1 h h_2 =>
  MinSearch.Initialisation_1.wf_0 SS SS mm1 xx SS h h_2
next exact fun SS done1 mm1 done mm xx mi mi1 h h_3 h_4 =>
  MinSearch.Operation_step_2.wf_0 SS done1 mm1 mm1 SS h h_3 h_4
next exact fun SS done1 mm1 done mm xx mi mi1 h h_8 h_9 h_10 h_11 h_12 h_13 h_14 =>
  MinSearch.Operation_step_2.wf_0 SS done1 mm1 mm1 SS h h_8 h_9
next
  intros
  expose_names
  exact min.WF_of_union
    (MinSearch.Operation_step_2.wf_0 SS done1 mm1 mm1 SS h h_1 h_2)
    min.WF_singleton
next
  intros
  expose_names
  subst_eqs
  exact min.WF_of_union
    (MinSearch.Operation_step_2.wf_0 SS done1 mm1 mm1 SS h h_1 h_2)
    (min.WF_of_finite h_13)
next grind
next
  intros
  expose_names
  subst_eqs
  exact min.WF_of_union
    (MinSearch.Operation_step_2.wf_0 SS done1 mm1 mm1 SS h h_1 h_2)
    min.WF_singleton
next
  intros
  expose_names
  subst_eqs
  exact min.WF_of_union
    (MinSearch.Operation_step_2.wf_0 SS done1 mm1 mm1 SS h h_1 h_2)
    (min.WF_of_finite h_13)
next grind
next grind
next
  intros
  expose_names
  exact MinSearch.Initialisation_0 SS xx h h_1
next
  intros
  expose_names
  exact MinSearch.Initialisation_1 SS SS mm1 xx SS h h_1
next grind
next
  intros
  expose_names
  subst_eqs
  exact FIN₁.of_union h_1 (FIN₁.singleton_mem (Set.mem_of_mem_inter_left h_10))
next grind
next
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  generalize_proofs min_wf at h_3
  rw [min.of_insert _ min_wf]
  split_ifs with hlt
  · rfl
  · rw [←h_3, not_le] at hlt
    nomatch lt_irrefl _ (lt_trans hlt h_11)
next
  intros
  expose_names
  subst_eqs
  use {xx}, ?_, rfl, ?_
  · exact FIN₁.singleton_mem h_10
  · generalize_proofs min_wf at h_3
    simp only [Set.union_singleton]
    rw [min.of_insert _ min_wf]
    split_ifs with hlt
    · rfl
    · rw [←h_3, not_le] at hlt
      nomatch lt_irrefl _ (lt_trans hlt h_11)
next grind
next grind
next grind
next grind
next
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  generalize_proofs min_wf at h_3
  rw [min.of_insert _ min_wf]
  split_ifs with hlt
  · rfl
  · rw [←h_3, not_le] at hlt
    nomatch lt_irrefl _ (lt_trans hlt h_11)
next
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  exact FIN₁.of_insert (Set.mem_of_mem_inter_left h_10) (Set.mem_of_mem_inter_left h_1)
next
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  generalize_proofs min_wf at h_3
  rw [min.of_insert _ min_wf]
  split_ifs with hlt
  · exact le_antisymm (Int.not_lt.mp h_11) (le_of_le_of_eq hlt h_3.symm)
  · exact h_3
next
  intros
  expose_names
  subst_eqs
  use {xx}, ?_, rfl, ?_
  · exact FIN₁.singleton_mem h_10
  · generalize_proofs min_wf at h_3
    simp only [Set.union_singleton]
    rw [min.of_insert _ min_wf]
    split_ifs with hlt
    · exact le_antisymm (le_of_le_of_eq hlt h_3.symm) (Int.not_lt.mp h_11)
    · rw [h_3]
next grind
next grind
next grind
next grind

prove_obligations_of MinSearch_r2
next
  intros
  expose_names
  exact card.WF_of_finite' h
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_refl 1, h_2.1⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_refl 1, h_2.1⟩
next
  intros
  expose_names
  subst_eqs
  simp only [Set.Icc_self, Set.mem_singleton_iff] at h_6
  subst jj
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_refl 1, h_2.1⟩
next
  intros
  expose_names
  subst_eqs
  exact min.WF_of_finite h_6
next
  intros
  expose_names
  subst_eqs
  exact min.WF_of_finite h_6
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_17.1, le_trans h_17.2 h_12.2⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_28.1, le_trans h_28.2 h_23.2⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_29.1, le_trans h_29.2 h_24.2⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_21.1, le_trans h_21.2 h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_28.1, le_trans h_28.2 h_23.2⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_29.1, le_trans h_29.2 h_24.2⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_21.1, le_trans h_21.2 h_18⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_27.1, le_trans h_27.2 h_22.2⟩
next
  intros
  expose_names
  subst_eqs
  exact app.WF_of_mem_tfun h_4.2 ⟨h_28.1, le_trans h_28.2 h_23.2⟩
next
  intros
  expose_names
  subst_eqs
  exact ⟨Int.le_refl 1, h_2.1⟩
next
  intros
  expose_names
  subst_eqs
  apply app.mem_ran
next
  intros
  expose_names
  subst_eqs
  use 1, ⟨Int.le_refl 1, Int.le_refl 1⟩, app.pair_app_mem
next
  intros
  expose_names
  subst_eqs
  rw [interval.of_singleton_eq, Set.mem_singleton_iff] at h_6
  subst jj
  apply le_refl
next
  intros
  expose_names
  subst_eqs
  rw [tfun_dom_eq h_4.2]
  exact ⟨Int.le_refl 1, h_2.1⟩
next
  intros
  expose_names
  subst_eqs
  rw [tfun_dom_eq h_4.2]
  exact h_4.2.1
next
  intros
  expose_names
  subst_eqs
  rw [interval.of_singleton_eq]
  ext x
  simp only [Set.mem_singleton_iff, SetRel.mem_image, exists_eq_left]
  constructor
  · rintro rfl
    exact app.pair_app_mem
  · intro h
    symm
    exact app.of_pair_eq _ h
next
  intros
  expose_names
  subst_eqs
  rw [tfun.ran_eq h_4.2, Set.ext_iff] at h_19
  simp only [SetRel.mem_image, Set.mem_Icc] at h_19
  apply le_antisymm
  · exact h_12.2
  · by_contra! contr
    have : app.WF tab (ii1 + 1) := by
      refine ⟨?_, ?_⟩
      · rw [tfun_dom_eq h_4.2]
        exact h_4.2
      · rw [tfun_dom_eq h_4.2]
        exact ⟨Int.le_add_one h_12.1, contr⟩
    have := app.mem_ran this
    rw [←h_18] at this
    rw [SetRel.mem_image] at this
    obtain ⟨i', ⟨_, hi'⟩, hxi'⟩ := this
    obtain rfl := h_4.1.2 hxi' app.pair_app_mem
    rw [Int.add_one_le_iff] at hi'
    nomatch lt_irrefl _ hi'
next
  intros
  expose_names
  subst_eqs
  exists tab(ii1+1)'(app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩)
  use ?_, ?_, ?_
  · simp only [Set.mem_diff, Set.mem_setOf_eq, SetRel.mem_image, Set.mem_Icc, not_exists, not_and,
    and_imp]
    and_intros
    · exact ⟨ii1 + 1, app.pair_app_mem⟩
    · intro i hi hi' contr
      rw [app.of_pair_iff (app.WF_of_mem_tfun h_4.2 ⟨hi, le_trans hi' h_12.2⟩)] at contr
      generalize_proofs wf_i wf_ii1 at contr
      have : i = ii1 + 1 := by
        apply h_4.1.2
        · rw [app.of_pair_iff wf_i]
        · rw [app.of_pair_iff wf_ii1, contr]
      rw [this, Int.add_one_le_iff] at hi'
      nomatch lt_irrefl _ hi'
  · intro
    use ⟨Int.le_add_one h_12.1, h_18⟩, ⟨ii1 + 1, app.pair_app_mem⟩, ?_, rfl, ?_, ?_
    · rw [Set.union_singleton]
      ext k
      simp only [Set.mem_insert_iff, SetRel.mem_image, Set.mem_Icc]
      constructor
      · rintro (rfl | ⟨i, hi, h⟩)
        · exact ⟨ii1 + 1, ⟨Int.le_add_one h_12.1, Int.le_refl (ii1 + 1)⟩, app.pair_app_mem⟩
        · exact ⟨i, ⟨hi.1, le_trans hi.2 (Int.le.intro 1 rfl)⟩, h⟩
      · rintro ⟨i, ⟨hi, hi'⟩, h⟩
        rw [Int.le_add_one_iff] at hi'
        obtain hi' | rfl := hi'
        · right
          use i, ⟨hi, hi'⟩, h
        · left
          symm
          rwa [app.of_pair_iff (app.WF_of_mem_tfun h_4.right ⟨Int.le_add_one h_12.left, h_18⟩)] at h
    · use ii1 + 1, ⟨Int.le_add_one h_12.1, Int.le_refl (ii1 + 1)⟩, app.pair_app_mem
    · rintro jj ⟨le_jj, hjj⟩
      rw [Int.le_add_one_iff] at hjj
      obtain hjj | rfl := hjj
      · exact le_trans (Int.le_of_lt h_19) (h_17 jj ⟨le_jj, hjj⟩)
      · exact le_refl _
  · nofun
next
  intros
  expose_names
  subst_eqs
  exact ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  apply app.mem_ran
next
  intros
  expose_names
  subst_eqs
  ext xᵢ
  simp only [SetRel.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨i, ⟨hi, hi'⟩, hxᵢ⟩
    use i, ⟨hi, Int.le_add_one hi'⟩
  · rintro ⟨i, ⟨hi, hi'⟩, hxᵢ⟩
    have := app.mem_ran (app.WF_of_mem_tfun h_4.2 ⟨hi, le_trans hi' h_18⟩)
    conv_lhs at this => rw [←h_20]
    rw [SetRel.mem_image] at this
    obtain ⟨i', hi', hxi'⟩ := this
    generalize_proofs wf_i' at hxi'
    exists i', hi'
    obtain rfl := app.of_pair_eq wf_i' hxᵢ
    exact hxi'
next
  intros
  expose_names
  subst_eqs
  generalize_proofs app_wf at h_19
  have := app.mem_ran app_wf
  conv_lhs at this => rw [←h_20]
  rw [SetRel.mem_image] at this
  obtain ⟨i', hi', hxi'⟩ := this
  rw [app.of_pair_iff (app.WF_of_mem_tfun h_4.2 ⟨hi'.1, le_trans hi'.2 h_12.2⟩)] at hxi'
  specialize h_17 i' hi'
  rw [hxi'] at h_17
  nomatch lt_irrefl _ (Int.lt_of_le_of_lt h_17 h_19)
next
  intros
  expose_names
  subst_eqs
  simp
  use ii1 + 1, ⟨Int.le_add_one h_12.1, Int.le_refl (ii1 + 1)⟩, app.pair_app_mem
next
  intros
  expose_names
  subst_eqs
  obtain ⟨le_jj, h_21⟩ := h_21
  rw [Int.le_add_one_iff] at h_21
  obtain h_21 | rfl := h_21
  · specialize h_17 jj ⟨le_jj, h_21⟩
    exact le_trans (Int.le_of_lt h_19) h_17
  · exact le_refl _
next
  intros
  expose_names
  subst_eqs
  generalize_proofs app_wf at h_19
  use tab(ii1+1)'app_wf, ?_, ?_, ?_
  · rw [Int.not_gt_eq] at h_19
    apply And.intro (app.mem_ran app_wf)
    intro contr
    simp only [SetRel.mem_image, Set.mem_Icc] at contr
    obtain ⟨i', ⟨hi'₁, hi'₂⟩, hxi'⟩ := contr
    obtain rfl := h_4.1.2 hxi' app.pair_app_mem
    rw [Int.add_one_le_iff] at hi'₂
    nomatch lt_irrefl _ hi'₂
  · intro
    contradiction
  · intro
    use ⟨Int.le_add_one h_12.1, by exact h_18⟩, h_7, ?_, rfl, ?_
    · intro j ⟨le_jj, hj⟩
      rw [Int.le_add_one_iff] at hj
      obtain hj | rfl := hj
      · exact h_17 j ⟨le_jj, hj⟩
      · exact Int.not_lt.mp h_19
    · ext k
      simp only [Set.union_singleton, Set.mem_insert_iff, SetRel.mem_image, Set.mem_Icc]
      constructor
      · rintro (rfl | ⟨i, hi, ik⟩)
        · exact ⟨ii1 + 1, ⟨Int.le_add_one h_12.1, Int.le_refl (ii1 + 1)⟩, app.pair_app_mem⟩
        · exact ⟨i, ⟨hi.1, le_trans hi.2 (Int.le.intro 1 rfl)⟩, ik⟩
      · rintro ⟨i, ⟨hi₁, hi₂⟩, ik⟩
        rw [Int.le_add_one_iff] at hi₂
        obtain hi₂ | rfl := hi₂
        · right
          use i, ⟨hi₁, hi₂⟩, ik
        · left
          symm
          rwa [app.of_pair_iff (app.WF_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩)] at ik
    · simp only [SetRel.mem_image, Set.mem_Icc] at h_16 ⊢
      obtain ⟨i, ⟨hi₁, hi₂⟩, hxi⟩ := h_16
      use i, ⟨hi₁, Int.le_add_one hi₂⟩, hxi
next
  intros
  expose_names
  subst_eqs
  exact ⟨Int.le_add_one h_12.1, h_18⟩
next
  intros
  expose_names
  subst_eqs
  rw [tfun.ran_eq h_4.2] at h_20
  apply subset_antisymm
  · intro x hx
    rw [SetRel.mem_image] at hx
    obtain ⟨i, ⟨hi, hi'⟩, hx⟩ := hx
    exists i, ⟨hi, Int.le_add_one hi'⟩
  · rw [h_20]
    intro x hx
    rw [SetRel.mem_image] at hx
    obtain ⟨i, ⟨hi, hi'⟩, hx⟩ := hx
    exists i, ⟨hi, Int.le_trans hi' h_18⟩
next
  intros
  expose_names
  subst_eqs
  apply image_mono (A := 1..ii1)
  · rintro i ⟨h, h'⟩
    exact ⟨h, Int.le_add_one h'⟩
  · exact h_16
next
  intros
  expose_names
  subst_eqs
  rw [Int.not_lt] at h_19
  obtain ⟨le_jj, h_21⟩ := h_21
  rw [Int.le_add_one_iff] at h_21
  obtain h_21 | rfl := h_21
  · apply h_17
    exact ⟨le_jj, h_21⟩
  · exact h_19
next
  intros
  expose_names
  subst_eqs
  obtain rfl : nn = ii1 := by
    rw [Int.not_lt] at h_18
    exact le_antisymm h_18 h_12.2
  rw [tfun.ran_eq h_4.2] at h_19
  contradiction
