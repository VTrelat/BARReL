import Barrel

open B.Builtins

namespace Leader

/-- A parent relation whose inverse-closed sets containing the root cover every node
cannot contain a pair of opposite edges. -/
theorem rooted_tree_asymmetric {α : Type*} {nodes : Set α} {root : α}
    {parent : SetRel α α}
    (htotal : parent ∈ (nodes \ {root}) ⟶ nodes)
    (hroot : root ∈ nodes)
    (hconnected : ∀ S ⊆ nodes, root ∈ S → (parent⁻¹)[S] ⊆ S → nodes ⊆ S) :
    parent ∩ parent⁻¹ = ∅ := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hab, hba⟩
  have ha := (htotal.1.1 hab).1
  have hb := (htotal.1.1 hba).1
  have hclosed : (parent⁻¹)[nodes \ {a, b}] ⊆ nodes \ {a, b} := by
    rintro z ⟨w, hw, hzw⟩
    refine ⟨(htotal.1.1 hzw).1.1, ?_⟩
    intro hz
    have hfun := htotal.1.2
    simp only [SetRel.mem_inv, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at *
    grind only
  have hroot' : root ∈ nodes \ {a, b} := by
    simpa [eq_comm] using And.intro hroot (And.intro ha.2 hb.2)
  have hall := hconnected (nodes \ {a, b}) Set.sdiff_subset hroot' hclosed
  simpa using (hall ha.1).2

end Leader
