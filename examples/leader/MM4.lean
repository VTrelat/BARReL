import examples.leader.MM3Support
import examples.leader.MM4Support

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

-- Store local summaries of the message, acknowledgement, and tree relations.
import refinement mm4 from "specs/leader"

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _ hnode
  exact app.WD_of_mem_tfun (Leader.tfun_const_product (B := 𝒫 ND) (Set.empty_subset ND)) hnode

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hba_total _ _ hedge
  exact app.WD_of_mem_tfun hba_total (hmsg_partial.1 hedge).2

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hba_total _ _ hedge _ _
  exact app.WD_of_mem_tfun hba_total (hmsg_partial.1 hedge).2

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hba_total _ _ hedge _ _ _
  exact app.WD_of_mem_tfun hba_total (hmsg_partial.1 hedge).2

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hba_total _ _ hedge _ _ hnode
  apply app.WD_of_mem_tfun (Leader.tfun_override_singleton hba_total
    (hmsg_partial.1 hedge).2 ?_) hnode
  have hba_value := (hba_total.1.1 (app.pair_app_mem
    (wd := app.WD_of_mem_tfun hba_total (hmsg_partial.1 hedge).2))).2
  exact Set.union_subset hba_value (Set.singleton_subset_iff.mpr (hmsg_partial.1 hedge).1)

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ hsn_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpartial _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ hedge
  exact app.WD_of_mem_tfun hsn_total (hpartial.1 hedge).2

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ hsn_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpartial _ _ _ _ _ _ _ _ _ _ _
    hsn_glue htr_glue _ _ _ _ _ _ _ _ _ _ _ hedge_old
  apply app.WD_of_mem_tfun
  · simpa only [hsn_glue] using hsn_total
  · exact (hpartial.1 (htr_glue ▸ hedge_old)).2

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ hsn_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpartial _ _ _ _ _ _ _ _ _ _ _
    hsn_glue htr_glue _ _ _ _ _ _ _ _ _ _ _ hedge_old _
  apply app.WD_of_mem_tfun
  · simpa only [hsn_glue] using hsn_total
  · exact (hpartial.1 (htr_glue ▸ hedge_old)).2

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ hsn_total _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpartial _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ hedge _ _ _ _ _
  exact app.WD_of_mem_tfun hsn_total (hpartial.1 hedge).2

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _
  simp

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _
  exact Leader.tfun_const_product (B := 𝒫 ND) (Set.empty_subset ND)

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ hnode
  apply app.of_pair_eq
  simp [SetRel.image, SetRel.inv, hnode]

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _ hbm _ _ _ _ _ _ _ _
  rw [hbm]
  ext x
  simp [dom, exists_or]

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hbm _
    hba_inv _ hsource htarget hfresh hnew hneighbors
  subst sn msg ack
  refine ⟨xx, yy, hsource, htarget, ?_, ?_, hneighbors, rfl⟩
  · simpa only [← hbm] using hfresh
  · intro hack
    apply hnew
    rw [hba_inv xx hsource]
    exact ⟨xx, rfl, hack⟩

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hba_total _ _ hedge _ _
  apply Leader.tfun_override_singleton hba_total (hmsg_partial.1 hedge).2
  have hba_value := (hba_total.1.1 (app.pair_app_mem
    (wd := app.WD_of_mem_tfun hba_total (hmsg_partial.1 hedge).2))).2
  exact Set.union_subset hba_value (Set.singleton_subset_iff.mpr (hmsg_partial.1 hedge).1)

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ hba_total hba_inv _ hedge _ _ hnode
  by_cases heq : xx1 = yy
  · subst xx1
    rw [Leader.app_override_singleton_self, hba_inv yy (hmsg_partial.1 hedge).2]
    ext z
    simp
  · rw [Leader.app_override_singleton_of_ne heq _ (app.WD_of_mem_tfun hba_total hnode)]
    rw [hba_inv xx1 hnode]
    ext z
    simp [heq]

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ hbm _ hba_inv _ hedge hnew htarget
  subst msg ack
  have hnack : (xx, yy) ∉ ack1 := by
    intro hack
    apply hnew
    rw [hba_inv yy (hmsg_partial.1 hedge).2]
    exact ⟨yy, rfl, hack⟩
  refine ⟨xx, yy, ⟨hedge, hnack⟩, ?_, rfl⟩
  simpa only [← hbm] using htarget

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ hbm _ hba_inv _ hedge hnew htarget
  subst msg ack cnt
  have hnack : (xx, yy) ∉ ack1 := by
    intro hack
    apply hnew
    rw [hba_inv yy (hmsg_partial.1 hedge).2]
    exact ⟨yy, rfl, hack⟩
  refine ⟨xx, yy, ⟨hedge, hnack⟩, ?_, rfl⟩
  simpa only [← hbm] using htarget

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _ _ _ _ hbt _ _
  rw [hbt]
  ext x
  simp [dom, exists_or]

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _ _ _ _ hbt hedge hfresh
  subst ack tr
  refine ⟨xx, yy, hedge, ?_, rfl⟩
  simpa only [← hbt] using hfresh

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hedge hnew
  subst tr sn
  exact ⟨xx, yy, hedge, hnew, rfl⟩

next obligation by
  intro ND nb gg ff sn1 msg1 ack1 tr1 cnt1 ld1 ts ld sn tr msg ack cnt bm1 ba1 bt1 xx yy xx1
    _ _ _ _ _ _ _ _ _ _ _ _ hmsg_partial _ _ _ _ _ _ _ _ hcnt_msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ hbm _ _ _ _ _
  simpa only [hbm] using (Leader.dom_diff_of_subset_pfun hmsg_partial hcnt_msg).symm

qed mm4
