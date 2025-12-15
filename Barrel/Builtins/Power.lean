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
    theorem FIN.of_empty {α : Type _} {A : Set α} : ∅ ∈ FIN A := by
      and_intros
      · exact Set.empty_subset A
      · exact Set.finite_empty

    @[grind .]
    theorem FIN.of_finite_self {α : Type _} {A : Set α} (hA : A.Finite) : A ∈ FIN A :=
      ⟨subset_refl _, hA⟩

    @[grind .]
    theorem FIN₁.of_finite_nonempty_self {α : Type _} {A : Set α} (h : A.Finite) (h' : A.Nonempty) :
      A ∈ FIN₁ A := ⟨⟨subset_refl _, h⟩, h'⟩

    @[grind .]
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

    @[grind .]
    theorem FIN.of_insert {α : Type _} {S A : Set α} {a : α} (ha : a ∈ A)
        (hS : S ∈ FIN A) : insert a S ∈ FIN A := by
      and_intros
      · intro x h
        rw [Set.mem_insert_iff] at h
        rcases h with rfl | hSx
        · exact ha
        · exact hS.1 hSx
      · simpa only [Set.finite_insert] using hS.2

    @[grind .]
    theorem FIN₁.of_insert {α : Type _} {S A : Set α} {a : α} (ha : a ∈ A)
      (hS : S ∈ FIN A) : insert a S ∈ FIN₁ A := ⟨FIN.of_insert ha hS, Set.insert_nonempty a S⟩

    theorem FIN.of_union {α : Type _} {A B S : Set α} (hA : A ∈ FIN S) (hB : B ∈ FIN S) :
        A ∪ B ∈ FIN S := by
      and_intros
      · intro x h
        rw [Set.mem_union] at h
        obtain h | h := h
        · exact hA.1 h
        · exact hB.1 h
      · exact Set.Finite.union hA.2 hB.2

    theorem FIN₁.of_union {α : Type _} {A B S : Set α} (hA : A ∈ FIN₁ S) (hB : B ∈ FIN₁ S) :
      A ∪ B ∈ FIN₁ S := ⟨FIN.of_union hA.1 hB.1, Set.Nonempty.inl hA.2⟩

    @[grind ., mono]
    theorem FIN.mono {α : Type _} {A S T : Set α} (h : S ⊆ T) (hA : A ∈ FIN S) :
        A ∈ FIN T := ⟨subset_trans hA.left h, hA.2⟩

    @[grind ., mono]
    theorem FIN₁.mono {α : Type _} {A S T : Set α} (h : S ⊆ T) (hA : A ∈ FIN₁ S) :
        A ∈ FIN₁ T := ⟨FIN.mono h hA.1, hA.2⟩
  end Lemmas
end B.Builtins
