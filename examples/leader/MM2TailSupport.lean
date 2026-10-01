import Barrel

open B.Builtins

namespace Leader

/-- Adding graph edges to a parent relation preserves a complete description of a node's
neighbours: symmetry ensures that every new predecessor was already a neighbour. -/
theorem neighbours_after_union {α : Type*} {graph parent extra : SetRel α α}
    {a b : α} (hsymm : graph = graph⁻¹) (hextra : extra ⊆ graph)
    (hneighbours : graph[{a}] = (parent⁻¹)[{a}] ∪ {b}) :
    graph[{a}] = ((parent ∪ extra)⁻¹)[{a}] ∪ {b} := by
  apply Set.Subset.antisymm
  · rw [hneighbours]
    exact Set.union_subset_union_left _
      (SetRel.image_subset_image_left (SetRel.inv_mono Set.subset_union_left))
  · rintro z (⟨w, hw, hzw⟩ | hz)
    · rcases hzw with hold | hnew
      · exact hneighbours ▸ Or.inl ⟨w, hw, hold⟩
      · exact ⟨w, hw, (Set.ext_iff.mp hsymm (w, z)).mpr (hextra hnew)⟩
    · exact hneighbours ▸ Or.inr hz

end Leader
