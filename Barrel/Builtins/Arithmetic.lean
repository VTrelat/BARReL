import Barrel.Builtins.Init
import Barrel.Builtins.Power
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

  section Lemmas

  @[grind=, simp]
  theorem interval.of_singleton_eq (a : ℤ) : (a .. a) = {a} :=
    Set.Icc_self a

  theorem interval.finite (lo hi : ℤ) : (lo .. hi).Finite := Set.finite_Icc lo hi

  theorem interval.nonempty {lo hi : ℤ} (h : lo ≤ hi) : (lo .. hi).Nonempty :=
    Set.nonempty_Icc.mpr h

  theorem interval.FIN₁_mem {lo hi : ℤ} (h : lo ≤ hi) : lo .. hi ∈ FIN₁ INTEGER := by
    and_intros
    · exact fun _ _ => trivial
    · exact finite lo hi
    · exact nonempty h

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

  theorem max.WF_interval {lo hi : ℤ} (h : lo ≤ hi) : max.WF (lo..hi) := by
    exists hi
    and_intros <;> grind

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

  end Lemmas
end B.Builtins
