import examples.leader.MM0
import examples.leader.MM1Support
import examples.leader.MM2Support

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

import refinement mm1 from "specs/leader"

next obligation by
  -- Express the selected tree as membership in the graph of ff.
  simp only [← app.of_pair_iff]
  introv _ _
  intro _ _ hsymm _ _ _ hroot_spec hroot_total _ _ htrees_asymmetric _ _ hpartial hsaturated
    hasymmetric hroot hready
  obtain ⟨tree, htreeND, hpair⟩ := hroot_total.2 xx hroot
  obtain ⟨htree, hedges, hconnected⟩ := (hroot_spec xx tree hroot htreeND).mp hpair
  have htree_eq := Leader.rooted_tree_eq_of_saturated hroot htree hedges
    (htrees_asymmetric xx tree hroot htreeND hpair) hconnected hpartial hsaturated
    hasymmetric hsymm hready
  simpa [htree_eq] using hpair

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _ _
  simp [pfun]

next obligation by
  introv
  intro _ _ _ _ _ _ _ _ _ _
  simp [domRestr]

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ hgraph _ _ _ _ _ _ _ _ _ _ _ hpartial _ _ _ _ hedge hsource_fresh _ _
  exact Leader.pfun_union_singleton hpartial (hgraph hedge).1 (hgraph hedge).2 hsource_fresh

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsaturated _ _ _ _ hsource_fresh htarget_fresh hneighbors
  exact Leader.saturated_union_singleton hsaturated hsource_fresh htarget_fresh hneighbors

next obligation by
  simp only [← app.of_pair_iff]
  introv _
  intro _ hgraph _ hirreflexive _ _ _ _ _ _ _ _ _ _ _ hasymmetric _ _ hedge _ htarget_fresh
    _
  have hne : xx ≠ yy := by
    rintro rfl
    have hloop : (xx, xx) ∈ B.Builtins.id ND ∩ gg :=
      ⟨⟨xx, (hgraph hedge).1, rfl⟩, hedge⟩
    simp [hirreflexive] at hloop
  exact Leader.asymmetric_union_singleton hasymmetric htarget_fresh hne

qed mm1
