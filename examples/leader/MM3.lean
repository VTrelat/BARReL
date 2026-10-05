import examples.leader.MM3Support

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- Record the confirmations received at each node.
import refinement mm3 from "specs/leader"

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _ _ _ _ _ _ _ _ _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ hnode
  exact app.WD_of_mem_tfun
    (Leader.tfun_const_product (A := ND) (B := 𝒫 ND) (Set.empty_subset ND)) hnode

next obligation by
  simp only [Leader.app_subset_iff, ← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htree_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ hseen_total _ hedge
  exact app.WD_of_mem_tfun hseen_total (htree_partial.1 hedge).2

next obligation by
  intro nb ND gg ff msg1 ack1 tr1 cnt1 ld1 ts ld tr msg ack cnt sn1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htree_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ hedge _ hnode
  refine app.WD_of_mem_tfun (B := 𝒫 ND) ?_ hnode
  apply Leader.tfun_override_singleton hseen_total (htree_partial.1 hedge).2
  apply Set.union_subset
  · exact (hseen_total.1.1 (app.pair_app_mem (wd :=
      app.WD_of_mem_tfun hseen_total (htree_partial.1 hedge).2))).2
  · exact Set.singleton_subset_iff.mpr (htree_partial.1 hedge).1

next obligation by
  simp only [← app.of_pair_iff]
  introv _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _
  exact Leader.tfun_const_product (Set.empty_subset ND)

next obligation by
  simp only [Leader.app_subset_iff, ← app.of_pair_iff]
  introv _ _ _ _ _ _ _ _ _ _ _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _
  rintro s ⟨_, rfl⟩
  exact Set.empty_subset _

next obligation by
  intro nb ND gg ff msg1 ack1 tr1 cnt1 ld1 ts ld tr msg ack cnt sn1 xx yy xx1
    _ _ hsymm _ _ _ _ _ _ hneighbors _ _ htree_ack hack_msg hmsg_graph _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ hseen_subset hnode hready
  subst tr
  apply Set.Subset.antisymm
  · rw [← hneighbors xx hnode, hready]
    exact hseen_subset xx hnode
  · rw [hsymm]
    exact SetRel.image_subset_image_left
      (SetRel.inv_mono (htree_ack.trans (hack_msg.trans hmsg_graph)))

next obligation by
  intro nb ND gg ff msg1 ack1 tr1 cnt1 ld1 ts ld tr msg ack cnt sn1 xx yy xx1
    _ _ hsymm _ _ _ _ _ _ hneighbors _ _ htree_ack hack_msg hmsg_graph _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ hseen_subset hsource _ hfresh hno_reverse_ack hready
  subst tr msg ack
  have hneighborhood := (hneighbors xx hsource).symm.trans hready
  have hedge : (xx, yy) ∈ gg := by
    have : yy ∈ gg[{xx}] := by
      rw [hneighborhood]
      exact Or.inr rfl
    simpa using this
  have hfull : gg[{xx}] = (tr1⁻¹)[{xx}] ∪ {yy} := by
    apply Set.Subset.antisymm
    · rw [hneighborhood]
      exact Set.union_subset_union_left _ (hseen_subset xx hsource)
    · apply Set.union_subset
      · rw [hsymm]
        exact SetRel.image_subset_image_left
          (SetRel.inv_mono (htree_ack.trans (hack_msg.trans hmsg_graph)))
      · exact Set.singleton_subset_iff.mpr ⟨xx, rfl, hedge⟩
  exact ⟨xx, yy, hedge, hno_reverse_ack, hfull, hfresh, rfl⟩

next obligation by
  intro nb ND gg ff msg1 ack1 tr1 cnt1 ld1 ts ld tr msg ack cnt sn1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htree_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total _ hedge _
  apply Leader.tfun_override_singleton hseen_total (htree_partial.1 hedge).2
  apply Set.union_subset
  · exact (hseen_total.1.1 (app.pair_app_mem (wd :=
      app.WD_of_mem_tfun hseen_total (htree_partial.1 hedge).2))).2
  · exact Set.singleton_subset_iff.mpr (htree_partial.1 hedge).1

next obligation by
  intro nb ND gg ff msg1 ack1 tr1 cnt1 ld1 ts ld tr msg ack cnt sn1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htree_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_total hseen_subset hedge _ hnode
  by_cases heq : xx1 = yy
  · subst xx1
    rw [Leader.app_override_singleton_self]
    exact Set.union_subset (hseen_subset yy (htree_partial.1 hedge).2)
      (Set.singleton_subset_iff.mpr ⟨yy, rfl, hedge⟩)
  · rw [Leader.app_override_singleton_of_ne heq _ (app.WD_of_mem_tfun hseen_total hnode)]
    exact hseen_subset xx1 hnode

next obligation by
  simp only [Leader.app_subset_iff, ← app.of_pair_iff]
  introv
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hseen_subset _ _ hnode s hs
  exact (hseen_subset xx1 hnode s hs).trans
    (SetRel.image_subset_image_left (SetRel.inv_mono Set.subset_union_left))

qed mm3
