import Barrel

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

import machine MinSearch       from "specs/case_study"
import refinement MinSearch_r1 from "specs/case_study"
import refinement MinSearch_r2 from "specs/case_study"

prove_obligations_of MinSearch
next -- Initialisation_1: xx = min {xx}
  intros
  rw [min.of_singleton]
next -- Operation_step_2: done ∪ add ∈ FIN₁ SS
  intros
  exact FIN₁.of_union ‹_› (FIN₁.mono Set.diff_subset ‹_›)
next -- Operation_step_3: min (done ∪ add) ∈ SS
  introv
  have : done ∪ add ⊆ SS := by grind
  generalize_proofs min_wd
  grind

prove_obligations_of MinSearch_r1
next -- Initialisation_1: xx = min {xx}
  intros
  rw [min.of_singleton]
next -- Operation_step_3: done1 ∪ {xx} ∈ FIN₁ SS
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  grind
next -- Operation_step_5: xx = min (done1 ∪ {xx})
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  rw [min.of_insert _ (by wd_min), ←h_8, ite_cond_eq_true _ _ (eq_true <| Int.le_of_lt h_11)]
next -- Operation_step_6: ∃ add, … ∧' min (done ∪ add) = xx
  intros
  expose_names
  subst_eqs
  exists {xx}, FIN₁.singleton_mem h_10, rfl
  simp only [Set.union_singleton]
  rw [min.of_insert _ (by wd_min), ←h_8, ite_cond_eq_true _ _ (eq_true <| Int.le_of_lt h_11)]
next -- Operation_step_12: done1 ∪ {xx} ∈ FIN₁ SS
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  grind
next -- Operation_step_13: mm1 = min (done1 ∪ {xx})
  intros
  expose_names
  subst_eqs
  simp only [Set.union_singleton]
  rw [Int.not_lt, Int.le_iff_lt_or_eq] at h_11
  obtain hle | rfl := h_11
  · rw [min.of_insert _ (by wd_min), ←h_8, ite_cond_eq_false _ _ (eq_false <| Int.not_le.mpr hle)]
  · rw [min.of_insert _ (by wd_min), ←h_8, ite_cond_eq_true _ _ (eq_true <| Int.le_refl _)]
next -- Operation_step_14: ∃ add, … ∧' min (done ∪ add) = mm1
  intros
  expose_names
  subst_eqs
  exists {xx}, FIN₁.singleton_mem h_10, rfl
  simp only [Set.union_singleton]
  rw [Int.not_lt, Int.le_iff_lt_or_eq] at h_11
  obtain hle | rfl := h_11
  · rw [min.of_insert _ (by wd_min), ←h_8, ite_cond_eq_false _ _ (eq_false <| Int.not_le.mpr hle)]
  · rw [min.of_insert _ (by wd_min), ←h_8, ite_cond_eq_true _ _ (eq_true <| Int.le_refl _)]

prove_obligations_of MinSearch_r2
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
    have : app.WD tab (ii1 + 1) := by
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
  exists tab(ii1+1)'(app.WD_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩)
  use ?_, ?_, ?_
  · simp only [Set.mem_diff, Set.mem_setOf_eq, SetRel.mem_image, Set.mem_Icc, not_exists, not_and,
    and_imp]
    and_intros
    · exact ⟨ii1 + 1, app.pair_app_mem⟩
    · intro i hi hi' contr
      rw [app.of_pair_iff (app.WD_of_mem_tfun h_4.2 ⟨hi, le_trans hi' h_12.2⟩)] at contr
      generalize_proofs wd_i wd_ii1 at contr
      have : i = ii1 + 1 := by
        apply h_4.1.2
        · rw [app.of_pair_iff wd_i]
        · rw [app.of_pair_iff wd_ii1, contr]
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
          rwa [app.of_pair_iff (app.WD_of_mem_tfun h_4.right ⟨Int.le_add_one h_12.left, h_18⟩)] at h
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
    have := app.mem_ran (app.WD_of_mem_tfun h_4.2 ⟨hi, le_trans hi' h_18⟩)
    conv_lhs at this => rw [←h_20]
    rw [SetRel.mem_image] at this
    obtain ⟨i', hi', hxi'⟩ := this
    generalize_proofs wd_i' at hxi'
    exists i', hi'
    obtain rfl := app.of_pair_eq wd_i' hxᵢ
    exact hxi'
next
  intros
  expose_names
  subst_eqs
  generalize_proofs app_wd at h_19
  have := app.mem_ran app_wd
  conv_lhs at this => rw [←h_20]
  rw [SetRel.mem_image] at this
  obtain ⟨i', hi', hxi'⟩ := this
  rw [app.of_pair_iff (app.WD_of_mem_tfun h_4.2 ⟨hi'.1, le_trans hi'.2 h_12.2⟩)] at hxi'
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
  generalize_proofs app_wd at h_19
  use tab(ii1+1)'app_wd, ?_, ?_, ?_
  · rw [Int.not_gt_eq] at h_19
    apply And.intro (app.mem_ran app_wd)
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
          rwa [app.of_pair_iff (app.WD_of_mem_tfun h_4.2 ⟨Int.le_add_one h_12.1, h_18⟩)] at ik
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
