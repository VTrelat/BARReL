import Barrel.Builtins.Arithmetic
import Barrel.Builtins.Function
import Mathlib.Tactic.Monotonicity

namespace B.Builtins

  abbrev seq {α : Type _} (E : Set α) : Set (SetRel ℤ α) :=
    { s | ∃ n ∈ NATURAL, s ∈ 1..n ⟶ E }

  structure size.WD {α : Type _} (S : SetRel ℤ α) : Prop where
    isSeq : S ∈ seq (ran S)

  noncomputable abbrev size {α : Type _} (S : SetRel ℤ α) (wd : size.WD S) : ℤ :=
    Classical.choose wd.isSeq

  section Lemmas

    @[grind .]
    theorem size.WD_of_empty {α : Type _} : size.WD (∅ : SetRel ℤ α) where
      isSeq := by
        use 0
        and_intros
        · use 0
        · simp only [ran.of_empty, Set.mem_powerset_iff, Set.prod_empty, subset_refl]
        · nofun
        · simp only [interval, Int.reduceLE, not_false_eq_true, Set.Icc_eq_empty,
          Set.mem_empty_iff_false, ran.of_empty, and_self, exists_false, imp_self, implies_true]

    theorem size.WD_of_mem_seq {α : Type _} {E : Set α} {S : SetRel ℤ α}
        (hS : S ∈ seq E) : size.WD S where
      isSeq := by
        obtain ⟨n, hn, hS'⟩ := hS
        use n, hn
        have := tfun.of_pfun hS'.1
        rwa [tfun_dom_eq hS'] at this

  end Lemmas
end B.Builtins
