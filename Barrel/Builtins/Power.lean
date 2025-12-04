import Barrel.Builtins.Init
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

namespace B.Builtins
  abbrev POW₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ 𝒫 A | S.Nonempty }
  scoped prefix:250 "𝒫₁ " => POW₁

  abbrev FIN {α : Type _} (A : Set α) : Set (Set α) := { S ⊆ A | S.Finite }
  abbrev FIN₁ {α : Type _} (A : Set α) : Set (Set α) := { S ∈ FIN A | S.Nonempty }

  section Lemmas

    @[grind .]
    theorem FIN.of_finite_self {α : Type _} {A : Set α} (hA : A.Finite) : A ∈ FIN A :=
      ⟨subset_refl _, hA⟩

    @[grind .]
    theorem FIN₁.of_finite_nonempty_self {α : Type _} {A : Set α} (h : A.Finite) (h' : A.Nonempty) :
      A ∈ FIN₁ A := ⟨⟨subset_refl _, h⟩, h'⟩

    theorem FIN₁.singleton_mem {α : Type _} {a : α} {A : Set α} (ha : a ∈ A) :
        {a} ∈ FIN₁ A := by
      simpa

    theorem FIN.of_sub {α : Type _} {A B : Set α} {S : Set α} (h : S ∈ FIN A) (hsub : B ⊆ S) :
        B ∈ FIN A := by
      rw [Set.mem_setOf] at h ⊢
      obtain ⟨hS, Sfin⟩ := h
      and_intros
      · trans S
        · exact hsub
        · exact hS
      · exact Set.Finite.subset Sfin hsub

    theorem FIN₁.of_sub {α : Type _} {A B : Set α} {S : Set α} (h : S ∈ FIN₁ A) (hsub : B ⊆ S) (hB : B.Nonempty) :
        B ∈ FIN₁ A := by
      rw [Set.mem_setOf] at h ⊢
      obtain ⟨⟨hS, Sfin⟩, Snemp⟩ := h
      exact ⟨⟨fun _ => (hS <| hsub ·), Set.Finite.subset Sfin hsub⟩, hB⟩

    theorem FIN.of_inter {α : Type _} {A B : Set α} {S : Set α} (h : A ∈ FIN S ∨ B ∈ FIN S) :
        A ∩ B ∈ FIN S := by
      obtain h | h := h
        <;> [ skip ; rw [Set.inter_comm] ]
        <;> exact FIN.of_sub h Set.inter_subset_left

    theorem FIN₁.of_inter {α : Type _} {A B : Set α} {S : Set α} (h : A ∈ FIN₁ S ∨ B ∈ FIN₁ S) :
        A ∩ B ∈ FIN S := by
      obtain h | h := h
        <;> [ skip ; rw [Set.inter_comm] ]
        <;> exact FIN.of_sub (Set.mem_of_mem_inter_left h) Set.inter_subset_left

  end Lemmas
end B.Builtins
