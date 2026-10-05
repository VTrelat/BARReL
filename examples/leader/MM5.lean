import examples.leader.MM3Support

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- Separate messages awaiting acknowledgement, progress, and confirmation.
import refinement mm5 from "specs/leader"

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff]
  introv _ _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ hTR_relation _ _ _
  introv
  intro hconfirmation
  exact app.WD_of_mem_tfun hseen_total (hTR_relation hconfirmation).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_total _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_glue _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ hsource _ _
  rw [hacks_glue]
  exact app.WD_of_mem_tfun hacks_total hsource

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hseen_glue _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ hsource _ _ _
  rw [hseen_glue]
  exact app.WD_of_mem_tfun hseen_total hsource

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_total _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMSG_partial _ _ _ _ _ _ _ _ _
    hmessage
  exact app.WD_of_mem_tfun hacks_total (hMSG_partial.1 hmessage).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_total _ _
    _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_glue _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ hmessage
  rw [hacks_glue]
  exact app.WD_of_mem_tfun hacks_total (hmsg_partial.1 hmessage).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_total _ _
    _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_glue _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ hmessage _ _
  rw [hacks_glue]
  exact app.WD_of_mem_tfun hacks_total (hmsg_partial.1 hmessage).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_total _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMSG_partial _ _ _ _ _ _ _ _ _
    hmessage _ _ _ _ _ _ _
  exact app.WD_of_mem_tfun hacks_total (hMSG_partial.1 hmessage).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_total _ _
    _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacks_glue _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ hmessage
  rw [hacks_glue]
  exact app.WD_of_mem_tfun hacks_total (hmsg_partial.1 hmessage).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hACK_relation
    hTR_relation _ _ _ _ hack _ hconfirmation
  apply app.WD_of_mem_tfun hseen_total
  rcases hconfirmation with hold | hnew
  · exact (hTR_relation hold).2
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hnew
    exact (hACK_relation hack).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTR_relation
    _ _ _ _ hconfirmation _
  exact app.WD_of_mem_tfun hseen_total (hTR_relation hconfirmation).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTR_relation
    _ _ _ _ _ hremaining
  apply app.WD_of_overload hseen_total.1 pfun_of_singleton
  left
  rw [tfun_dom_eq hseen_total]
  exact (hTR_relation hremaining.1).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ htr_partial _ _ _ _ _ _ _ _ _ _ _ hseen_glue _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ hedge
  rw [hseen_glue]
  exact app.WD_of_mem_tfun hseen_total (htr_partial.1 hedge).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ htr_partial _ _ _ _ _ _ _ _ _ _ _ hseen_glue _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ hedge _
  rw [hseen_glue]
  exact app.WD_of_mem_tfun hseen_total (htr_partial.1 hedge).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTR_relation
    _ _ _ _ hconfirmation _ _ _ _
  exact app.WD_of_mem_tfun hseen_total (hTR_relation hconfirmation).2

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hseen_glue _ _ _ _ _ _ _ _ _ _ _
    _ _ _ hnode _
  rw [hseen_glue]
  exact app.WD_of_mem_tfun hseen_total hnode

next obligation by
  simp [pfun]

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsent_sources _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMSG_partial hmsg_partition _
    _ _ _ _ _ _ _ hsource htarget hsource_fresh _ _
  apply Leader.pfun_union_singleton hMSG_partial hsource htarget
  rintro ⟨receiver, hmessage⟩
  apply hsource_fresh
  rw [hsent_sources, hmsg_partition]
  exact ⟨receiver, Or.inl (Or.inl hmessage)⟩

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsent_sources _ _
    _ _ _ _ _ _ hack_msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMSG_ack_disjoint _
    _ _ _ _ _ _ _ _ hsource_fresh _ _
  rw [Set.union_inter_distrib_right, hMSG_ack_disjoint]
  simp only [Set.empty_union, Set.singleton_inter_eq_empty]
  intro hack
  apply hsource_fresh
  rw [hsent_sources]
  exact ⟨_, hack_msg hack⟩

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsent_sources _ _
    _ _ _ _ _ _ _ _ _ _ _ _ hcnt_msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMSG_cnt_disjoint
    _ _ _ _ _ _ _ _ hsource_fresh _ _
  rw [Set.union_inter_distrib_right, hMSG_cnt_disjoint]
  simp only [Set.empty_union, Set.singleton_inter_eq_empty]
  intro hcontention
  apply hsource_fresh
  rw [hsent_sources]
  exact ⟨_, hcnt_msg hcontention⟩

next obligation by
  intro ND nb gg ff bm1 msg ba1 bt1 tr sn1 ack cnt1 ld1 ts ld sn cnt bm ba bt MSG1 ACK1 TR1 xx
    yy xx1 yy1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ hmsg_partition _ _ _ _ _ _ _ _ hsource htarget hfresh
    hno_ack hready
  subst sn bm ba
  refine ⟨xx, yy, hsource, htarget, hfresh, hno_ack, hready, rfl, ?_⟩
  rw [hmsg_partition]
  ac_rfl

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hMSG_partial _ _ _ _ _ _ _ _ _ _ _ _
  exact Leader.pfun_of_subset hMSG_partial Set.sdiff_subset

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ hMSG_cnt_disjoint _ _ _ _ _ _ _ _ _
  apply Set.disjoint_iff_inter_eq_empty.mp
  exact Disjoint.mono_left Set.sdiff_subset
    (Set.disjoint_iff_inter_eq_empty.mpr hMSG_cnt_disjoint)

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hMSG_partial _ _ _ hACK_relation _ _ _ _ _ hmessage _ _
  exact Set.union_subset hACK_relation
    (Set.singleton_subset_iff.mpr (hMSG_partial.1 hmessage))

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htr_ack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ hMSG_ack_disjoint _ _ _ _ _ hACK_tr_disjoint _ hmessage _ _
  rw [Set.union_inter_distrib_right, hACK_tr_disjoint]
  simp only [Set.empty_union, Set.singleton_inter_eq_empty]
  intro hparent
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hMSG_ack_disjoint)
    hmessage (htr_ack hparent)

next obligation by
  intro ND nb gg ff bm1 msg ba1 bt1 tr sn1 ack cnt1 ld1 ts ld sn cnt bm ba bt MSG1 ACK1 TR1 xx
    yy xx1 yy1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ hmsg_partition hMSG_ack_disjoint _ _ _ _ hack_partition _ _
    hmessage hno_ack hreceiver_fresh
  subst bm ba
  have hmessage_abstract : (xx, yy) ∈ msg := by
    rw [hmsg_partition]
    exact Or.inl (Or.inl hmessage)
  refine ⟨xx, yy, hmessage_abstract, hno_ack, hreceiver_fresh, rfl, ?_, ?_, ?_⟩
  · calc
      msg = (MSG1 \ {(xx, yy)} ∪ {(xx, yy)}) ∪ ack ∪ cnt1 := by
        rw [Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hmessage), hmsg_partition]
      _ = MSG1 \ {(xx, yy)} ∪ (ack ∪ {(xx, yy)}) ∪ cnt1 := by ac_rfl
  · rw [Set.inter_union_distrib_left, Set.sdiff_inter_self, Set.union_empty,
      ← Set.inter_sdiff_right_comm, hMSG_ack_disjoint]
    simp
  · rw [hack_partition]
    ac_rfl

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hMSG_partial _ _ _ _ _ _ _ _ _ _ _ _
  exact Leader.pfun_of_subset hMSG_partial Set.sdiff_subset

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ hmsg_partition _ _ _ _ _ _ _ _ hmessage _ _
  have hrestore := Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hmessage)
  rw [hmsg_partition]
  conv_lhs => rw [← hrestore]
  ac_rfl

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ hMSG_ack_disjoint _ _ _ _ _ _ _ _ _ _
  apply Set.disjoint_iff_inter_eq_empty.mp
  exact Disjoint.mono_left Set.sdiff_subset
    (Set.disjoint_iff_inter_eq_empty.mpr hMSG_ack_disjoint)

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ hMSG_cnt_disjoint _ _ _ _ _ _ _ _ _
  apply Set.disjoint_iff_inter_eq_empty.mp
  apply Disjoint.union_right
  · exact Disjoint.mono_left Set.sdiff_subset
      (Set.disjoint_iff_inter_eq_empty.mpr hMSG_cnt_disjoint)
  · exact Set.disjoint_sdiff_left

next obligation by
  intro ND nb gg ff bm1 msg ba1 bt1 tr sn1 ack cnt1 ld1 ts ld sn cnt bm ba bt MSG1 ACK1 TR1 xx
    yy xx1 yy1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ hmsg_partition _ _ _ _ _ _ _ _ hmessage hno_ack
    hreceiver_active
  subst cnt bm ba
  refine ⟨xx, yy, ?_, hno_ack, hreceiver_active, rfl⟩
  rw [hmsg_partition]
  exact Or.inl (Or.inl hmessage)

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ hACK_relation _ _ _ _ _ _ _
  exact Set.sdiff_subset.trans hACK_relation

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ hACK_relation hTR_relation _ _ _ _ hack _
  exact Set.union_subset hTR_relation (Set.singleton_subset_iff.mpr (hACK_relation hack))

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ htree_sources _ hseen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hACK_relation _ _ _ _ hnot_seen hack hsource_fresh hconfirmation
  rcases hconfirmation with hold | hnew
  · exact hnot_seen xx1 yy1 hold
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hnew
    rintro ⟨seen, hseen_pair, hseen⟩
    have hparent : (xx, yy) ∈ tr := by
      simpa [SetRel.mem_image, SetRel.mem_inv] using
        hseen_spec yy (hACK_relation hack).2 seen hseen_pair hseen
    apply hsource_fresh
    rw [htree_sources]
    exact ⟨yy, hparent⟩

next obligation by
  intro ND nb gg ff bm1 msg ba1 bt1 tr sn1 ack cnt1 ld1 ts ld sn cnt bm ba bt MSG1 ACK1 TR1 xx
    yy xx1 yy1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ hTR_tree hack_partition hACK_tree_disjoint _ hack
    hsource_fresh
  subst bt
  have hack_abstract : (xx, yy) ∈ ack := by
    rw [hack_partition]
    exact Or.inl hack
  refine ⟨xx, yy, hack_abstract, hsource_fresh, rfl,
    Set.union_subset_union_left _ hTR_tree, ?_, ?_⟩
  · calc
      ack = (ACK1 \ {(xx, yy)} ∪ {(xx, yy)}) ∪ tr := by
        rw [Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hack), hack_partition]
      _ = ACK1 \ {(xx, yy)} ∪ (tr ∪ {(xx, yy)}) := by ac_rfl
  · rw [Set.inter_union_distrib_left, Set.sdiff_inter_self, Set.union_empty,
      ← Set.inter_sdiff_right_comm, hACK_tree_disjoint]
    simp

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ hTR_relation _ _ _ _ _
  exact Set.Subset.trans Set.sdiff_subset hTR_relation

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ hTR_tr _ _ _ _
  exact Set.Subset.trans Set.sdiff_subset hTR_tr

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yy xx1 yy1 _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hsn_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hTR_relation _ _ _ hTR_fresh _ hremaining
  by_cases htarget : yy1 = yy
  · subst yy1
    rw [Leader.app_override_singleton_self]
    rintro (hseen | heq)
    · exact hTR_fresh xx1 yy hremaining.1 hseen
    · apply hremaining.2
      simpa using heq
  · rw [Leader.app_override_singleton_of_ne htarget _
      (app.WD_of_mem_tfun hsn_total (hTR_relation hremaining.1).2)]
    exact hTR_fresh xx1 yy1 hremaining.1

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sn _ _ _ _ _ _ _ xx yy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTR_tr _ _ hTR_fresh
    hconfirmation
  subst sn
  exact ⟨xx, yy, hTR_tr hconfirmation, hTR_fresh xx yy hconfirmation, rfl⟩

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hcnt_glue hbm_glue _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [hbm_glue, hcnt_glue]

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_cnt_disjoint _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ hmsg_partition _ hMSG_cnt _ _ _ _ _ _ _ _
  subst cnt
  rw [hmsg_partition, Set.union_empty]
  apply Set.union_sdiff_cancel_right
  simp [Set.union_inter_distrib_right, hMSG_cnt, hack_cnt_disjoint]

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp

next obligation by
  simp only [← app.of_pair_iff, Leader.app_subset_iff, Leader.mem_app_iff]
  introv _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ hforward hreverse
  subst cnt
  exact ⟨xx, yy, hforward, hreverse⟩

next obligation by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hready
  subst sn
  exact hready

qed mm5
