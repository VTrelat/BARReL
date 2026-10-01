import Barrel

open B.Builtins

namespace Leader

/-- When every neighbour of the root points to it, a saturated partial orientation
    agrees with the rooted spanning tree. Connectivity propagates agreement from the root. -/
theorem rooted_tree_eq_of_saturated {α : Type*} {nodes : Set α}
    {graph tree forest : SetRel α α} {root : α}
    (hroot : root ∈ nodes)
    (htree : tree ∈ (nodes \ {root}) ⟶ nodes)
    (hedges : tree ⊆ graph)
    (hasym : tree ∩ tree⁻¹ = ∅)
    (hconnected : ∀ S ⊆ nodes, root ∈ S → (tree⁻¹)[S] ⊆ S → nodes ⊆ S)
    (hforest : forest ∈ nodes ⇸ nodes)
    (hsaturated : dom forest ◁ (forest ∪ forest⁻¹) = dom forest ◁ graph)
    (hforest_asym : forest ∩ forest⁻¹ = ∅)
    (hsymm : graph = graph⁻¹)
    (hready : graph[{root}] = (forest⁻¹)[{root}]) : tree = forest := by
  let S : Set α := {a ∈ nodes | a = root ∨ ∃ b, (a, b) ∈ tree ∧ (a, b) ∈ forest}
  have hS : S ⊆ nodes := fun _ h ↦ h.1
  have hrootS : root ∈ S := ⟨hroot, Or.inl rfl⟩
  have hclosed : (tree⁻¹)[S] ⊆ S := by
    rintro a ⟨b, hb, hab⟩
    refine ⟨(htree.1.1 hab).1.1, Or.inr ⟨b, hab, ?_⟩⟩
    have hba : (b, a) ∈ graph := (Set.ext_iff.mp hsymm (b, a)).mpr (hedges hab)
    rcases hb.2 with rfl | ⟨c, hbc, hbcForest⟩
    · simpa using (Set.ext_iff.mp hready a).mp ⟨b, rfl, hba⟩
    · have hbaForest := (Set.ext_iff.mp hsaturated (b, a)).mpr ⟨hba, c, hbcForest⟩
      rcases hbaForest.1 with hbaForest | habForest
      · have hac : a = c := hforest.2 hbaForest hbcForest
        subst c
        have hcycle : (b, a) ∈ tree ∩ tree⁻¹ := ⟨hbc, hab⟩
        simp [hasym] at hcycle
      · exact habForest
  have hall := hconnected S hS hrootS hclosed
  have hsub : tree ⊆ forest := by
    rintro ⟨a, b⟩ hab
    rcases (hall (htree.1.1 hab).1.1).2 with rfl | ⟨c, hac, hacForest⟩
    · exact False.elim ((htree.1.1 hab).1.2 rfl)
    · have hbc := htree.1.2 hab hac
      simpa [hbc] using hacForest
  have hrootNot : root ∉ dom forest := by
    rintro ⟨b, hb⟩
    have hrootGraph := (Set.ext_iff.mp hsaturated (root, b)).mp ⟨Or.inl hb, b, hb⟩
    have hrev : (b, root) ∈ forest := by
      simpa using (Set.ext_iff.mp hready b).mp ⟨root, rfl, hrootGraph.1⟩
    have hcycle : (root, b) ∈ forest ∩ forest⁻¹ := ⟨hb, hrev⟩
    simp [hforest_asym] at hcycle
  apply Set.Subset.antisymm hsub
  rintro ⟨a, b⟩ hab
  have ha : a ∈ nodes \ {root} := by
    refine ⟨(hforest.1 hab).1, ?_⟩
    rintro rfl
    exact hrootNot ⟨b, hab⟩
  obtain ⟨c, -, hac⟩ := htree.2 a ha
  have hbc := hforest.2 hab (hsub hac)
  simpa [hbc] using hac

/-- Adding a parent at a fresh node preserves saturation once its other neighbours
    have already chosen it as parent. -/
theorem saturated_union_singleton {α : Type*} {graph forest : SetRel α α} {x y : α}
    (hsaturated : dom forest ◁ (forest ∪ forest⁻¹) = dom forest ◁ graph)
    (hfresh : x ∉ dom forest) (hfreshY : y ∉ dom forest)
    (hready : graph[{x}] = (forest⁻¹)[{x}] ∪ {y}) :
    dom (forest ∪ {(x, y)}) ◁ (forest ∪ {(x, y)} ∪ (forest ∪ {(x, y)})⁻¹) =
      dom (forest ∪ {(x, y)}) ◁ graph := by
  ext ⟨a, b⟩
  have hold := Set.ext_iff.mp hsaturated (a, b)
  have hnew := Set.ext_iff.mp hready b
  simp only [domRestr, dom, Set.mem_setOf_eq, Set.mem_union, SetRel.mem_inv] at hold
  simp only [SetRel.mem_image, Set.mem_singleton_iff, exists_eq_left, Set.mem_union,
    SetRel.mem_inv] at hnew
  change (¬ ∃ z, (x, z) ∈ forest) at hfresh
  change (¬ ∃ z, (y, z) ∈ forest) at hfreshY
  simp only [domRestr, dom, Set.mem_setOf_eq, Set.mem_union, SetRel.mem_inv,
    Set.mem_singleton_iff, Prod.mk.injEq]
  grind only

/-- A new edge creates no opposite pair when its target has no parent and is distinct. -/
theorem asymmetric_union_singleton {α : Type*} {forest : SetRel α α} {x y : α}
    (hasym : forest ∩ forest⁻¹ = ∅) (hfresh : y ∉ dom forest) (hne : x ≠ y) :
    (forest ∪ {(x, y)}) ∩ (forest ∪ {(x, y)})⁻¹ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨a, b⟩ ⟨hab, hba⟩
  have hold := Set.ext_iff.mp hasym (a, b)
  simp only [Set.mem_inter_iff, SetRel.mem_inv, Set.mem_empty_iff_false, iff_false,
    not_and] at hold
  simp only [Set.mem_union, SetRel.mem_inv, Set.mem_singleton_iff, Prod.mk.injEq] at hab hba
  change (¬ ∃ z, (y, z) ∈ forest) at hfresh
  grind only

end Leader
