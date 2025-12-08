import Barrel.Builtins.Init
import Barrel.Builtins.Power
import Barrel.Builtins.Function
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Defs

namespace B.Builtins
  open Classical

  abbrev interval (lo hi : ℤ) : Set Int := Set.Icc lo hi
  scoped infixl:170 ".." => interval

  structure min.WF {α : Type _} [LinearOrder α] (S : Set α) : Prop where
    isBoundedBelow : ∃ x ∈ S, ∀ y ∈ S, x ≤ y

  noncomputable abbrev min {α : Type _} [LinearOrder α] (S : Set α) (wf : min.WF S) : α :=
    Classical.choose wf.isBoundedBelow

  structure max.WF {α : Type _} [LinearOrder α] (S : Set α) : Prop where
    isBoundedAbove : ∃ x ∈ S, ∀ y ∈ S, y ≤ x

  noncomputable abbrev max {α : Type _} [LinearOrder α] (S : Set α) (wf : max.WF S) : α :=
    Classical.choose wf.isBoundedAbove

  structure card.WF {α : Type _} (S : Set α) : Prop where
    isFinite : S.Finite

  noncomputable abbrev card {α : Type _} (S : Set α) (wf : card.WF S) : ℤ :=
    have : Fintype S := @Fintype.ofFinite _ wf.isFinite
    S.toFinset.card

  section Lemmas

    @[grind =, simp]
    theorem NAT.eq_interval : NAT = (0 .. MAXINT) := rfl

    @[grind =, simp]
    theorem NAT₁.eq_interval : NAT₁ = (1 .. MAXINT) := rfl

    @[grind =, simp]
    theorem INT.eq_interval : INT = (MININT .. MAXINT) := rfl

    @[grind=, simp]
    theorem interval.of_singleton_eq (a : ℤ) : (a .. a) = {a} :=
      Set.Icc_self a

    @[grind .]
    theorem interval.finite (lo hi : ℤ) : (lo .. hi).Finite := Set.finite_Icc lo hi

    @[grind .]
    theorem interval.nonempty {lo hi : ℤ} (h : lo ≤ hi) : (lo .. hi).Nonempty :=
      Set.nonempty_Icc.mpr h

    theorem interval.FIN_mem {lo hi : ℤ} : lo .. hi ∈ FIN INTEGER := by
      and_intros
      · exact fun _ _ => trivial
      · exact finite lo hi

    theorem interval.FIN₁_mem {lo hi : ℤ} (h : lo ≤ hi) : lo .. hi ∈ FIN₁ INTEGER :=
      ⟨FIN_mem, interval.nonempty h⟩


    @[grind .]
    theorem NAT.Finite : NAT.Finite := by
      rw [eq_interval]
      apply interval.finite

    @[grind .]
    theorem NAT.mem_FIN : NAT ∈ FIN INTEGER := interval.FIN_mem

    @[grind .]
    theorem NAT.mem_FIN₁ : NAT ∈ FIN₁ INTEGER := interval.FIN₁_mem (Int.zero_le_ofNat _)

    @[grind =, simp]
    theorem NAT.pow_eq_fin : 𝒫 NAT = FIN NAT := by
      ext S
      rw [eq_interval, Set.mem_powerset_iff]
      constructor <;> intro hS
      · exact FIN.of_sub ⟨subset_refl _, interval.finite _ _⟩ hS
      · exact hS.1

    @[grind =, simp]
    theorem NAT₁.pow_eq_fin : 𝒫 NAT₁ = FIN NAT₁ := by
      ext S
      rw [eq_interval, Set.mem_powerset_iff]
      constructor <;> intro hS
      · exact FIN.of_sub ⟨subset_refl _, interval.finite _ _⟩ hS
      · exact hS.1

    @[grind =, simp]
    theorem INT.pow_eq_fin : 𝒫 INT = FIN INT := by
      ext S
      rw [eq_interval, Set.mem_powerset_iff]
      constructor <;> intro hS
      · exact FIN.of_sub ⟨subset_refl _, interval.finite _ _⟩ hS
      · exact hS.1

    @[grind =, simp]
    theorem NAT.pow₁_eq_fin₁ : 𝒫₁ NAT = FIN₁ NAT := by
      ext S
      rw [eq_interval, Set.mem_setOf_eq, Set.mem_powerset_iff]
      constructor <;> intro hS
      · apply FIN₁.of_sub
        · exact FIN₁.of_finite_nonempty_self
            (interval.finite _ _)
            (interval.nonempty (Int.zero_le_ofNat _))
        · exact hS.1
        · exact hS.2
      · exact ⟨hS.1.1, hS.2⟩

    @[grind =, simp]
    theorem NAT₁.pow₁_eq_fin₁ : 𝒫₁ NAT₁ = FIN₁ NAT₁ := by
      ext S
      rw [eq_interval, Set.mem_setOf_eq, Set.mem_powerset_iff]
      constructor <;> intro hS
      · apply FIN₁.of_sub
        · exact FIN₁.of_finite_nonempty_self
            (interval.finite _ _)
            (interval.nonempty (Int.zero_le_ofNat _))
        · exact hS.1
        · exact hS.2
      · exact ⟨hS.1.1, hS.2⟩

    @[grind =, simp]
    theorem INT.pow₁_eq_fin₁ : 𝒫₁ INT = FIN₁ INT := by
      ext S
      rw [eq_interval, Set.mem_setOf_eq, Set.mem_powerset_iff]
      constructor <;> intro hS
      · apply FIN₁.of_sub
        · exact FIN₁.of_finite_nonempty_self
            (interval.finite _ _)
            (interval.nonempty (Int.zero_le_ofNat _))
        · exact hS.1
        · exact hS.2
      · exact ⟨hS.1.1, hS.2⟩

    @[grind .]
    theorem NAT₁.Finite : NAT₁.Finite := by
      rw [eq_interval]
      apply interval.finite

    @[grind .]
    theorem INT.Finite : INT.Finite := by
      rw [eq_interval]
      apply interval.finite

    @[grind., simp]
    theorem min.WF_NATURAL : min.WF NATURAL := by
      exists 0
      and_intros
      · rw [Builtins.NATURAL, Set.mem_setOf]
      · intro y hy
        rwa [Set.mem_setOf] at hy

    theorem min.WF_of_finite {α : Type _} [LinearOrder α] {S A : Set α} (h : S ∈ FIN₁ A) :
        min.WF S := by
      let fin := Set.Finite.to_subtype h.1.2
      let nemp := Set.Nonempty.to_subtype h.2
      obtain ⟨x, h⟩ := Finite.exists_min (@_root_.id ↑S)
      exact ⟨x, Subtype.coe_prop x, fun y hy ↦ h ⟨y, hy⟩⟩

    theorem max.WF_of_finite {α : Type _} [LinearOrder α] {S A : Set α} (h : S ∈ FIN₁ A) :
        max.WF S := by
      let fin := Set.Finite.to_subtype h.1.2
      let nemp := Set.Nonempty.to_subtype h.2
      obtain ⟨x, h⟩ := Finite.exists_max (@_root_.id ↑S)
      exact ⟨x, Subtype.coe_prop x, fun y hy ↦ h ⟨y, hy⟩⟩

    @[grind .]
    theorem max.WF_interval {lo hi : ℤ} (h : lo ≤ hi) : max.WF (lo..hi) := by
      exists hi
      and_intros <;> grind

    @[grind .]
    theorem min.WF_interval {lo hi : ℤ} (h : lo ≤ hi) : min.WF (lo..hi) := by
      exists lo
      and_intros <;> grind

    @[grind ., simp]
    theorem interval.min_eq {lo hi : Int} (h : lo ≤ hi) :
        min (lo .. hi) (min.WF_interval h) = lo := by
      unfold min
      generalize_proofs hm
      obtain ⟨m_def, m_is_min⟩ := Classical.choose_spec hm
      exact le_antisymm (m_is_min _ (Set.left_mem_Icc.mpr h)) m_def.1

    @[grind ., simp]
    theorem interval.max_eq {lo hi : Int} (h : lo ≤ hi) :
        max (lo .. hi) (max.WF_interval h) = hi := by
      unfold max
      generalize_proofs hm
      obtain ⟨m_def, m_is_max⟩ := Classical.choose_spec hm
      exact le_antisymm m_def.2 (m_is_max _ (Set.right_mem_Icc.mpr h))

    theorem min.WF_singleton {α : Type _} [LinearOrder α] {a : α} : min.WF {a} :=
      min.WF_of_finite <| FIN₁.singleton_mem (Set.mem_singleton a)

    theorem max.WF_singleton {α : Type _} [LinearOrder α] {a : α} : max.WF {a} :=
      max.WF_of_finite <| FIN₁.singleton_mem (Set.mem_singleton a)

    @[simp]
    theorem min.of_singleton {α : Type _} [LinearOrder α] {a : α} :
        min {a} (min.WF_singleton) = a := by
      unfold min
      generalize_proofs ha
      exact (Classical.choose_spec ha).1

    @[simp]
    theorem max.of_singleton {α : Type _} [LinearOrder α] {a : α} :
        max {a} (max.WF_singleton) = a := by
      unfold max
      generalize_proofs ha
      exact (Classical.choose_spec ha).1

    @[grind ., simp]
    theorem card.WF_of_empty {α : Type _} : card.WF (∅ : Set α) where
      isFinite := Set.finite_empty

    @[grind ., simp]
    theorem card.WF_of_interval {lo hi : ℤ} : card.WF (lo .. hi) where
      isFinite := interval.finite lo hi

    @[grind ., simp]
    theorem card.of_empty {α : Type _} : card (∅ : Set α) (card.WF_of_empty) = 0 := by
      simp only [card, Set.toFinset_empty, Finset.card_empty, Nat.cast_zero]

    @[grind ., simp]
    theorem card.of_interval {lo hi : ℤ} :
        card (lo .. hi) (card.WF_of_interval) = Max.max (hi + 1 - lo) 0 := by
      simp only [card, Set.toFinset_Icc, Int.card_Icc, Int.ofNat_toNat]

    @[grind .]
    theorem card.WF_of_subset {α : Type _} {S T : Set α} (hS : S ⊆ T)
        (hT : card.WF T) : card.WF S where
      isFinite := Set.Finite.subset hT.isFinite hS

    @[grind →]
    theorem card.mono {α : Type _} {S T : Set α} (hS : S ⊆ T) (hT : card.WF T) :
        card S (card.WF_of_subset hS hT) ≤ card T hT := by
      rw [Int.ofNat_le]
      apply Finset.card_le_card
      have : Finite ↑S := (card.WF_of_subset hS hT).isFinite
      have : Finite ↑T := hT.isFinite
      exact @Set.toFinset_mono α S T (Fintype.ofFinite ↑S) (Fintype.ofFinite ↑T) hS

  end Lemmas
end B.Builtins
