import B4Lean.Builtins

import Mathlib.Data.Fintype.Basic

namespace B.Builtins
  open Classical

namespace WF

@[grind., simp]
theorem min.NATURAL : min.WF NATURAL := by
  exists 0
  and_intros
  · rw [Builtins.NATURAL, Set.mem_setOf]
  · intro y hy
    rwa [Set.mem_setOf] at hy

@[grind, simp]
theorem of_finite {α : Type _} [LinearOrder α] {S : Set α} (h : S.Finite) : min.WF S := by
  have := Set.Finite.to_subtype h
  refine { isBoundedBelow := ?_ }
  have := Finite.exists

end WF


end B.Builtins
