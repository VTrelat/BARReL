import Barrel

open B.Builtins

namespace Leader

/-- Removing some edges from a partial function removes exactly their sources. -/
lemma dom_diff_of_subset_pfun {α β : Type*} {A : Set α} {B : Set β}
    {f g : Set (α × β)} (hf : f ∈ A ⇸ B) (hgf : g ⊆ f) :
    dom (f \ g) = dom f \ dom g := by
  ext x
  constructor
  · rintro ⟨y, hy, hnot⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    rintro ⟨z, hz⟩
    have heq := hf.2 hy (hgf hz)
    subst z
    exact hnot hz
  · rintro ⟨⟨y, hy⟩, hnot⟩
    exact ⟨y, hy, fun h ↦ hnot ⟨y, h⟩⟩

end Leader
