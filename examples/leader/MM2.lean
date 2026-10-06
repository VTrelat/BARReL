import examples.leader.MM1
import examples.leader.MM2Support
import examples.leader.MM2TailSupport

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

set_option maxHeartbeats 50000 in
import refinement mm2 from "specs/leader"

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _ _ _
  intro _ _ _ hirreflexive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg hmsg_graph _ _ _ _ _ _ _ _
  exact Leader.inter_id_eq_empty_of_subset hirreflexive (hack_msg.trans hmsg_graph)

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _ _ _
  intro _ _ _ hirreflexive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_graph _ _ _ _ _ _ _ _
  exact Leader.inter_id_eq_empty_of_subset hirreflexive hmsg_graph

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _ _ _
  intro _ _ _ hirreflexive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htr_ack hack_msg hmsg_graph _ _ _ _ _ _ _
    _
  exact Leader.inter_id_eq_empty_of_subset hirreflexive (htr_ack.trans (hack_msg.trans hmsg_graph))

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _
  simp

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ hgraph _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hedge _
    _ hsource_fresh
  exact Leader.pfun_union_singleton hmsg_partial (hgraph hedge).1 (hgraph hedge).2 hsource_fresh

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_graph _ _ _ _ _ _ _ _ _ _ _ hedge _ _ _
    hpending
  exact (Set.union_subset hmsg_graph (Set.singleton_subset_iff.mpr hedge)) hpending.1

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htr_ack hack_msg _ hpending_ready _ _ _ _ _ _ _ _ _
    _ _ _ _ hsource_fresh hpending
  rcases hpending with ⟨hmessage | hmessage, hnot_ack⟩
  · exact (hpending_ready xx1 yy1 ⟨hmessage, hnot_ack⟩).2.1
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hmessage
    rintro ⟨z, hz⟩
    exact hsource_fresh ⟨z, hack_msg (htr_ack hz)⟩

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ hsymm _ _ _ _ _ _ hsaturated _ _ _ _ _ _ _ _ _ _ htr_ack hack_msg _ hpending_ready _ _ _
    _ _ _ _ _ _ _ hedge hno_reverse_ack _ hsource_fresh hpending
  rcases hpending with ⟨hmessage | hmessage, hnot_ack⟩
  · exact (hpending_ready xx1 yy1 ⟨hmessage, hnot_ack⟩).2.2.1
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hmessage
    exact Leader.send_target_unattached hsymm hsaturated htr_ack hack_msg hedge
      hno_reverse_ack hsource_fresh

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_ready _ _ _ _ _ _ _ _ _ _ _ _
    hneighbors _ hpending
  rcases hpending with ⟨hmessage | hmessage, hnot_ack⟩
  · exact (hpending_ready xx1 yy1 ⟨hmessage, hnot_ack⟩).2.2.2
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hmessage
    exact hneighbors

next obligation by
  simp only [← app.of_pair_iff]
  introv
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hother_neighbors _ _ _ _ _ _ _ _ _
    hneighbors _ hmessage hneighbor hdistinct
  rcases hmessage with hmessage | hmessage
  · exact hother_neighbors xx1 yy1 hmessage zz hneighbor hdistinct
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hmessage
    rw [hneighbors] at hneighbor
    simpa [hdistinct, SetRel.mem_image, SetRel.mem_inv] using hneighbor

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcnt_msg hpending_not_contention _ _ _
    _ _ _ _ _ hsource_fresh hpending hreceiver_fresh
  rcases hpending with ⟨hmessage | hmessage, hnot_ack⟩
  · apply hpending_not_contention xx1 yy1 ⟨hmessage, hnot_ack⟩
    rintro ⟨z, hz⟩
    exact hreceiver_fresh ⟨z, Or.inl hz⟩
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hmessage
    intro hc
    exact hsource_fresh ⟨yy, hcnt_msg hc⟩

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ hsymm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htr_ack hack_msg hmsg_graph _ _ _
    hother_neighbors _ _ _ hpending_reciprocal _ _ _ hedge hno_reverse_ack hneighbors hsource_fresh
    hpending hreceiver_active
  exact Leader.send_preserves_reciprocity hsymm htr_ack hack_msg hmsg_graph
    hother_neighbors hpending_reciprocal
    hedge hno_reverse_ack hneighbors hsource_fresh hpending hreceiver_active

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ hack_msg _ _ _ _ _ _ _ _ _ _ _ _
    hpending _
  apply Leader.pfun_of_subset hmsg_partial
  exact Set.union_subset hack_msg (Set.singleton_subset_iff.mpr hpending.1)

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_ready _ _ _ _ _ _ _ _ _ _ _ _
    hpending_new
  have hpending_old : (xx1, yy1) ∈ msg1 \ ack1 :=
    ⟨hpending_new.1, fun hack ↦ hpending_new.2 (Or.inl hack)⟩
  exact (hpending_ready xx1 yy1 hpending_old).2.1

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_ready _ _ _ _ _ _ _ _ _ _ _ _
    hpending_new
  have hpending_old : (xx1, yy1) ∈ msg1 \ ack1 :=
    ⟨hpending_new.1, fun hack ↦ hpending_new.2 (Or.inl hack)⟩
  exact (hpending_ready xx1 yy1 hpending_old).2.2.1

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg hmsg_graph _ _ _ _ _ _ _ _ _ _ _
    hpending _ hack_new _
  exact hmsg_graph (Set.union_subset hack_msg (Set.singleton_subset_iff.mpr hpending.1) hack_new)

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_ready hack_ready _ _ _ _ _ _ _ _ _
    hpending _ hack_new hsource_fresh
  rcases hack_new with hack_old | hsent
  · exact (hack_ready xx1 yy1 hack_old hsource_fresh).2.2.1
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hsent
    exact (hpending_ready xx yy hpending).2.2.1

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_ready hack_ready _ _ _ _ _ _ _ _ _
    hpending _ hack_new hsource_fresh
  rcases hack_new with hack_old | hsent
  · exact (hack_ready xx1 yy1 hack_old hsource_fresh).2.2.2
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hsent
    exact (hpending_ready xx yy hpending).2.2.2

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg _ _ _ hack_asymmetric _ _ _ _ _ _ _ _
    hpending htarget_fresh
  apply Leader.asymmetric_union_singleton_of_no_reverse hack_asymmetric
  · intro reverse
    exact htarget_fresh ⟨xx, hack_msg reverse⟩
  · intro same
    exact htarget_fresh ⟨yy, same ▸ hpending.1⟩

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_not_contention _ _ _ _ _ _
    _ hpending_new hreceiver_fresh
  have hpending_old : (xx1, yy1) ∈ msg1 \ ack1 :=
    ⟨hpending_new.1, fun hack ↦ hpending_new.2 (Or.inl hack)⟩
  exact hpending_not_contention xx1 yy1 hpending_old hreceiver_fresh

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_not_contention
    hack_cnt_disjoint _ _ _ _ hpending htarget_fresh
  rw [Set.union_inter_distrib_right, hack_cnt_disjoint]
  simp [hpending_not_contention xx yy hpending htarget_fresh]

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_reciprocal _ _ _ _
    htarget_fresh hpending_new hreceiver_active
  have hpending_old : (xx1, yy1) ∈ msg1 \ ack1 :=
    ⟨hpending_new.1, fun hack ↦ hpending_new.2 (Or.inl hack)⟩
  have hreverse := hpending_reciprocal xx1 yy1 hpending_old hreceiver_active
  refine ⟨hreverse.1, ?_⟩
  rintro (hack | hnew)
  · exact hreverse.2 hack
  · have hsource_eq := (Prod.mk.inj (Set.mem_singleton_iff.mp hnew)).2
    have hsender_active : xx1 ∈ dom msg1 := ⟨yy1, hpending_new.1⟩
    exact htarget_fresh (hsource_eq ▸ hsender_active)

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpending_not_contention _ _ _ _ _ _
    htarget_active hpending_other hreceiver_fresh
  rintro (hcontention | hnew)
  · exact hpending_not_contention xx1 yy1 hpending_other hreceiver_fresh hcontention
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hnew
    exact hreceiver_fresh htarget_active

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_cnt_disjoint _ _ _ _ hpending
    _
  rw [Set.inter_union_distrib_left, hack_cnt_disjoint]
  simp [hpending.2]

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ hack_msg _ hpending_ready _ _ _ _ _ _ _
    _ _ _ hack _ hpending
  have hready := hpending_ready xx1 yy1 hpending
  rintro ⟨z, hz | hz⟩
  · exact hready.2.1 ⟨z, hz⟩
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hz
    have hsame_target := hmsg_partial.2 hpending.1 (hack_msg hack)
    exact hpending.2 (hsame_target ▸ hack)

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ hack_msg _ hpending_ready _ _ _ _ _ _
    hpending_reciprocal _ _ _ hack _ hpending
  have hready := hpending_ready xx1 yy1 hpending
  rintro ⟨z, hz | hz⟩
  · exact hready.2.2.1 ⟨z, hz⟩
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hz
    have hreverse := hpending_reciprocal xx1 xx hpending ⟨yy, hack_msg hack⟩
    have hsame_target := hmsg_partial.2 hreverse.1 (hack_msg hack)
    exact hreverse.2 (hsame_target ▸ hack)

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ hsymm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg hmsg_graph hpending_ready _ _ _ _ _ _
    _ _ _ _ hack _ hpending
  exact Leader.neighbours_after_union hsymm
    (Set.singleton_subset_iff.mpr (hmsg_graph (hack_msg hack)))
    (hpending_ready xx1 yy1 hpending).2.2.2

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ hsymm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg hmsg_graph _ hack_ready
    hack_asymmetric hother_neighbors _ _ _ _ _ _ _ hack _ hack_pair hnew_source_fresh
  have hfresh : xx1 ∉ dom tr1 := fun ⟨z, hz⟩ ↦ hnew_source_fresh ⟨z, Or.inl hz⟩
  have hready := hack_ready xx1 yy1 hack_pair hfresh
  rintro ⟨z, hz | hz⟩
  · exact hready.2.2.1 ⟨z, hz⟩
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hz
    have hne : xx1 ≠ yy := by
      rintro rfl
      have hcycle : (xx, xx1) ∈ ack1 ∩ ack1⁻¹ := ⟨hack, hack_pair⟩
      simp [hack_asymmetric] at hcycle
    have hlink : xx1 ∈ gg[{xx}] :=
      ⟨xx, rfl, (Set.ext_iff.mp hsymm (xx, xx1)).mpr (hmsg_graph (hack_msg hack_pair))⟩
    exact hfresh ⟨xx, hother_neighbors xx yy (hack_msg hack) xx1 hlink hne⟩

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ hsymm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg hmsg_graph _ hack_ready _ _ _ _ _ _ _
    _ _ hack _ hack_pair hnew_source_fresh
  have hfresh : xx1 ∉ dom tr1 := fun ⟨z, hz⟩ ↦ hnew_source_fresh ⟨z, Or.inl hz⟩
  exact Leader.neighbours_after_union hsymm
    (Set.singleton_subset_iff.mpr (hmsg_graph (hack_msg hack)))
    (hack_ready xx1 yy1 hack_pair hfresh).2.2.2

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_ready _ _ _ _ _ _ _ _ _ hack
    hsource_fresh
  subst tr
  obtain ⟨hedge, hx, hy, hneighbors⟩ := hack_ready xx yy hack hsource_fresh
  exact ⟨xx, yy, hedge, hx, hy, hneighbors, rfl⟩

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact Leader.pfun_of_subset hmsg_partial Set.sdiff_subset

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hack_msg _ _ _ _ _ _ _ hack_cnt_disjoint _ _ _ _ _
    _
  exact Set.subset_sdiff.mpr ⟨hack_msg, Set.disjoint_iff_inter_eq_empty.mpr hack_cnt_disjoint⟩

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact Set.inter_empty ack1

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ hpending_reciprocal _
    _ _ _ _ hpending hreceiver_active
  obtain ⟨z, hz⟩ := hreceiver_active
  have hreverse := hpending_reciprocal xx1 yy1 ⟨hpending.1.1, hpending.2⟩ ⟨z, hz.1⟩
  refine ⟨⟨hreverse.1, ?_⟩, hreverse.2⟩
  have hsame_target := hmsg_partial.2 hz.1 hreverse.1
  simpa [hsame_target] using hz.2

qed mm2
