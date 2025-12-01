import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

namespace B.Builtins
  abbrev POW₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ 𝒫 A | S.Nonempty }
  scoped prefix:250 "𝒫₁ " => POW₁

  abbrev FIN {α : Type _} (A : Set α) : Set (Set α) := { S ⊆ A | S.Finite }
  abbrev FIN₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ FIN A | S.Nonempty }

  section Lemmas

    theorem FIN₁.singleton_mem {α : Type _} {a : α} {A : Set α} (ha : a ∈ A) :
        {a} ∈ FIN₁ A := by
      simpa

  end Lemmas
end B.Builtins
