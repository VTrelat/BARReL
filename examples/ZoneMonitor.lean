import examples.ZoneMonitorAutomation
import examples.ZoneMonitorProofs
import examples.ZoneMonitorSourceWD

open B.Builtins ZoneMonitorSupport

-- This POG includes Atelier B's source WD obligations, including read-only operations.
set_option maxHeartbeats 20000 in
import pog ZoneMonitor from "specs/zonemonitor"

obligation Operation_Record_9.wd_12 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[dom ({(ss, vv)} : SetRel ℤ ℤ)] := by
    rw [image_dom_singleton zone ss vv (app.WD_of_mem_tfun h_2 h_16)]
    exact h_18.2
  rw [readings_overload hz]
  exact min_WD_available h_10 h.1.2 (h_15 zz h_18.1).1

obligation Operation_Record_10.wd_11 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[dom ({(ss, vv)} : SetRel ℤ ℤ)] := by
    rw [image_dom_singleton zone ss vv (app.WD_of_mem_tfun h_2 h_16)]
    exact h_18.2
  rw [readings_overload hz]
  exact max_WD_available h_10 h.1.2 (h_15 zz h_18.1).1

obligation Operation_RecordBatch_15.wd_11 of ZoneMonitor by
  intros
  expose_names
  rw [readings_overload h_17.2]
  exact min_WD_available h_10 h.1.2 (h_15 zz h_17.1).1

obligation Operation_RecordBatch_16.wd_10 of ZoneMonitor by
  intros
  expose_names
  rw [readings_overload h_17.2]
  exact max_WD_available h_10 h.1.2 (h_15 zz h_17.1).1

obligation Operation_Withdraw_21.wd_12 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[{ss}] := by
    rw [app.image_singleton_eq_of_wd (app.WD_of_mem_tfun h_2 (pfun.dom_subset h_10 h_16))]
    exact h_17.2
  rw [readings_domSubtr hz]
  exact min_WD_available h_10 h.1.2 (h_15 zz h_17.1).1

obligation Operation_Withdraw_22.wd_11 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[{ss}] := by
    rw [app.image_singleton_eq_of_wd (app.WD_of_mem_tfun h_2 (pfun.dom_subset h_10 h_16))]
    exact h_17.2
  rw [readings_domSubtr hz]
  exact max_WD_available h_10 h.1.2 (h_15 zz h_17.1).1

obligation Operation_Configure_29.wd_11 of ZoneMonitor by
  intros
  expose_names
  exact min_WD_available h_10 h.1.2 (h_15 zz1 h_20.1).1

obligation Operation_Configure_30.wd_10 of ZoneMonitor by
  intros
  expose_names
  exact max_WD_available h_10 h.1.2 (h_15 zz1 h_20.1).1

obligation Operation_Authorize_34.wd_17 of ZoneMonitor by
  intros
  expose_names
  apply min_WD_available h_10 h.1.2
  rcases h_21 with hz | hz
  · exact (h_15 zz1 hz).1
  · have he : zz1 = zz := hz
    simpa only [he] using h_17

obligation Operation_Authorize_35.wd_16 of ZoneMonitor by
  intros
  expose_names
  apply max_WD_available h_10 h.1.2
  rcases h_21 with hz | hz
  · exact (h_15 zz1 hz).1
  · have he : zz1 = zz := hz
    simpa only [he] using h_17

obligation Operation_Revoke_39.wd_11 of ZoneMonitor by
  intros
  expose_names
  exact min_WD_available h_10 h.1.2 (h_15 zz1 h_17.1).1

obligation Operation_Revoke_40.wd_10 of ZoneMonitor by
  intros
  expose_names
  exact max_WD_available h_10 h.1.2 (h_15 zz1 h_17.1).1


obligation Operation_Authorize_33.wd_16 of ZoneMonitor by
  intros
  expose_names
  apply app.WD_of_mem_tfun h_3
  rcases h_21 with hz | hz
  · exact h_13 hz
  · have he : zz1 = zz := hz
    simpa only [he] using h_16

obligation Operation_Authorize_34.wd_16 of ZoneMonitor by
  intros
  expose_names
  apply app.WD_of_mem_tfun h_11
  rcases h_21 with hz | hz
  · exact h_13 hz
  · have he : zz1 = zz := hz
    simpa only [he] using h_16

obligation Operation_Authorize_35.wd_17 of ZoneMonitor by
  intros
  expose_names
  apply app.WD_of_mem_tfun h_12
  rcases h_21 with hz | hz
  · exact h_13 hz
  · have he : zz1 = zz := hz
    simpa only [he] using h_16

obligation Initialisation_0 of ZoneMonitor by
  intros
  exact ⟨Set.empty_subset _, by simp⟩

obligation Operation_RecordBatch_13 of ZoneMonitor by
  intros
  expose_names
  change available (reading <+ batch) zone zz ≠ ∅
  rw [available_overload h_17.2]
  exact (h_15 zz h_17.1).1

obligation Operation_RecordBatch_14 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, hcard, _hmin, _hmax⟩ := h_15 zz h_17.1
  simpa only [available_overload h_17.2] using hcard

obligation Operation_RecordBatch_15 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, _hcard, hmin, _hmax⟩ := h_15 zz h_17.1
  simpa only [readings_overload h_17.2] using hmin

obligation Operation_RecordBatch_16 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, _hcard, _hmin, hmax⟩ := h_15 zz h_17.1
  simpa only [readings_overload h_17.2] using hmax

obligation Operation_Record_7 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[dom ({(ss, vv)} : SetRel ℤ ℤ)] := by
    rw [image_dom_singleton zone ss vv (app.WD_of_mem_tfun h_2 h_16)]
    exact h_18.2
  obtain ⟨hne, _hcard, _hmin, _hmax⟩ := h_15 zz h_18.1
  simpa only [available_overload hz] using hne

obligation Operation_Record_8 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[dom ({(ss, vv)} : SetRel ℤ ℤ)] := by
    rw [image_dom_singleton zone ss vv (app.WD_of_mem_tfun h_2 h_16)]
    exact h_18.2
  obtain ⟨_hne, hcard, _hmin, _hmax⟩ := h_15 zz h_18.1
  simpa only [available_overload hz] using hcard

obligation Operation_Record_9 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[dom ({(ss, vv)} : SetRel ℤ ℤ)] := by
    rw [image_dom_singleton zone ss vv (app.WD_of_mem_tfun h_2 h_16)]
    exact h_18.2
  obtain ⟨_hne, _hcard, hmin, _hmax⟩ := h_15 zz h_18.1
  simpa only [readings_overload hz] using hmin

obligation Operation_Record_10 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[dom ({(ss, vv)} : SetRel ℤ ℤ)] := by
    rw [image_dom_singleton zone ss vv (app.WD_of_mem_tfun h_2 h_16)]
    exact h_18.2
  obtain ⟨_hne, _hcard, _hmin, hmax⟩ := h_15 zz h_18.1
  simpa only [readings_overload hz] using hmax

obligation Operation_Withdraw_19 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[{ss}] := by
    rw [app.image_singleton_eq_of_wd (app.WD_of_mem_tfun h_2 (pfun.dom_subset h_10 h_16))]
    exact h_17.2
  obtain ⟨hne, _hcard, _hmin, _hmax⟩ := h_15 zz h_17.1
  simpa only [available_domSubtr hz] using hne

obligation Operation_Withdraw_20 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[{ss}] := by
    rw [app.image_singleton_eq_of_wd (app.WD_of_mem_tfun h_2 (pfun.dom_subset h_10 h_16))]
    exact h_17.2
  obtain ⟨_hne, hcard, _hmin, _hmax⟩ := h_15 zz h_17.1
  simpa only [available_domSubtr hz] using hcard

obligation Operation_Withdraw_21 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[{ss}] := by
    rw [app.image_singleton_eq_of_wd (app.WD_of_mem_tfun h_2 (pfun.dom_subset h_10 h_16))]
    exact h_17.2
  obtain ⟨_hne, _hcard, hmin, _hmax⟩ := h_15 zz h_17.1
  simpa only [readings_domSubtr hz] using hmin

obligation Operation_Withdraw_22 of ZoneMonitor by
  intros
  expose_names
  have hz : zz ∉ zone[{ss}] := by
    rw [app.image_singleton_eq_of_wd (app.WD_of_mem_tfun h_2 (pfun.dom_subset h_10 h_16))]
    exact h_17.2
  obtain ⟨_hne, _hcard, _hmin, hmax⟩ := h_15 zz h_17.1
  simpa only [readings_domSubtr hz] using hmax

obligation Operation_Configure_23 of ZoneMonitor by
  intros
  expose_names
  exact tfun_overload_singleton h_11 h_16 h_17

obligation Operation_Configure_24 of ZoneMonitor by
  intros
  expose_names
  exact tfun_overload_singleton h_12 h_16 h_18

obligation Operation_Configure_26 of ZoneMonitor by
  intros
  expose_names
  by_cases he : zz1 = zz
  · subst zz1
    simpa only [app_overload_singleton_self] using h_19
  · have hl := app.WD_of_mem_tfun h_11 h_20
    have hu := app.WD_of_mem_tfun h_12 h_20
    simpa only [app_overload_singleton_other he hl, app_overload_singleton_other he hu]
      using h_14 zz1 h_20

obligation Operation_Configure_27 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨hne, _hcard, _hmin, _hmax⟩ := h_15 zz1 h_20.1
  exact hne

obligation Operation_Configure_28 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, hcard, _hmin, _hmax⟩ := h_15 zz1 h_20.1
  exact hcard

obligation Operation_Configure_29 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, _hcard, hmin, _hmax⟩ := h_15 zz1 h_20.1
  have he : zz1 ≠ zz := h_20.2
  have hw := app.WD_of_mem_tfun h_11 (h_13 h_20.1)
  simpa only [app_overload_singleton_other he hw] using hmin

obligation Operation_Configure_30 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, _hcard, _hmin, hmax⟩ := h_15 zz1 h_20.1
  have he : zz1 ≠ zz := h_20.2
  have hw := app.WD_of_mem_tfun h_12 (h_13 h_20.1)
  simpa only [app_overload_singleton_other he hw] using hmax

obligation Operation_Authorize_32 of ZoneMonitor by
  intros
  expose_names
  rcases h_21 with hz | hz
  · obtain ⟨hne, _hcard, _hmin, _hmax⟩ := h_15 zz1 hz
    exact hne
  · have he : zz1 = zz := hz
    subst zz1
    exact h_17

obligation Operation_Authorize_33 of ZoneMonitor by
  intros
  expose_names
  rcases h_21 with hz | hz
  · obtain ⟨_hne, hcard, _hmin, _hmax⟩ := h_15 zz1 hz
    exact hcard
  · have he : zz1 = zz := hz
    subst zz1
    exact h_18

obligation Operation_Authorize_34 of ZoneMonitor by
  intros
  expose_names
  rcases h_21 with hz | hz
  · obtain ⟨_hne, _hcard, hmin, _hmax⟩ := h_15 zz1 hz
    exact hmin
  · have he : zz1 = zz := hz
    subst zz1
    exact h_19

obligation Operation_Authorize_35 of ZoneMonitor by
  intros
  expose_names
  rcases h_21 with hz | hz
  · obtain ⟨_hne, _hcard, _hmin, hmax⟩ := h_15 zz1 hz
    exact hmax
  · have he : zz1 = zz := hz
    subst zz1
    exact h_20

obligation Operation_Revoke_37 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨hne, _hcard, _hmin, _hmax⟩ := h_15 zz1 h_17.1
  exact hne

obligation Operation_Revoke_38 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, hcard, _hmin, _hmax⟩ := h_15 zz1 h_17.1
  exact hcard

obligation Operation_Revoke_39 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, _hcard, hmin, _hmax⟩ := h_15 zz1 h_17.1
  exact hmin

obligation Operation_Revoke_40 of ZoneMonitor by
  intros
  expose_names
  obtain ⟨_hne, _hcard, _hmin, hmax⟩ := h_15 zz1 h_17.1
  exact hmax

obligation Operation_Record_5 of ZoneMonitor by
  intros
  expose_names
  exact pfun_overload_same h_10 (pfun_singleton h_16 h_17)

obligation Operation_RecordBatch_11 of ZoneMonitor by
  intros
  expose_names
  exact pfun_overload_same h_10 h_16

obligation Operation_Withdraw_17 of ZoneMonitor by
  intros
  expose_names
  exact pfun_domSubtr h_10 {ss}

obligation WellDefinednessInvariant_45 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.mem_dom_of_tfun <;> assumption

obligation WellDefinednessInvariant_46 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessInvariant_47 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.mem_dom_of_tfun <;> assumption

obligation WellDefinednessInvariant_48 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessInvariant_49 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.mem_dom_of_tfun
  · assumption
  · solve_by_elim (maxDepth := 3) only [*, Set.mem_of_mem_of_subset]

obligation WellDefinednessInvariant_50 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessInvariant_51 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.available_FIN_self <;> assumption

obligation WellDefinednessInvariant_53 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessInvariant_54 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.readings_ne_empty
  assumption

obligation WellDefinednessInvariant_55 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.image_inter_diff_FIN
  · assumption
  · exact B.Builtins.interval.finite _ _

obligation WellDefinednessInvariant_57 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.image_inter_FIN
  · assumption
  · exact B.Builtins.interval.finite _ _

obligation WellDefinednessInvariant_59 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinedness_Record_60 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.mem_dom_of_tfun <;> assumption

obligation WellDefinedness_Record_61 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinedness_Withdraw_62 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.mem_dom_of_tfun
  · assumption
  · apply ZoneMonitorSourceWD.mem_source_of_mem_dom <;> assumption

obligation WellDefinedness_Withdraw_63 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessPrecondition_Authorize_64 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.mem_dom_of_tfun <;> assumption

obligation WellDefinednessPrecondition_Authorize_65 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessPrecondition_Authorize_66 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.available_FIN_self <;> assumption

obligation WellDefinednessPrecondition_Authorize_68 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinednessPrecondition_Authorize_69 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.readings_ne_empty
  assumption

obligation WellDefinednessPrecondition_Authorize_70 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.image_inter_diff_FIN
  · assumption
  · exact B.Builtins.interval.finite _ _

obligation WellDefinednessPrecondition_Authorize_72 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.image_inter_FIN
  · assumption
  · exact B.Builtins.interval.finite _ _

obligation WellDefinednessPrecondition_Authorize_74 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  exact B.Builtins.pfun.of_tfun (by assumption)

obligation WellDefinedness_ReadSensor_75 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.pfun_own_dom_ran
  assumption

obligation WellDefinedness_ZoneSummary_76 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.available_FIN_self <;> assumption

obligation WellDefinedness_ZoneSummary_77 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.readings_ne_empty
  assumption

obligation WellDefinedness_ZoneSummary_78 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.image_inter_diff_FIN
  · assumption
  · exact B.Builtins.interval.finite _ _

obligation WellDefinedness_ZoneSummary_79 of ZoneMonitor by
  intros
  generalize_proofs at *
  apply ZoneMonitorSourceWD.image_inter_FIN
  · assumption
  · exact B.Builtins.interval.finite _ _

qed ZoneMonitor
