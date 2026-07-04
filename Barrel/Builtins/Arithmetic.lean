import Barrel.Builtins.Init
import Barrel.Builtins.Power
import Barrel.Builtins.Function
import Barrel.Builtins.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Defs
import Barrel.Tactics
namespace B.Builtins
  open Classical

  abbrev interval (lo hi : ℤ) : Set Int := Set.Icc lo hi
  scoped infixl:170 ".." => interval

  structure min.WD {α : Type _} [PartialOrder α] (S : Set α) : Prop where
    isBoundedBelow : ∃ x ∈ S, ∀ y ∈ S, x ≤ y

  noncomputable abbrev min {α : Type _} [PartialOrder α] (S : Set α) (wd : min.WD S) : α :=
    Classical.choose wd.isBoundedBelow

  structure max.WD {α : Type _} [PartialOrder α] (S : Set α) : Prop where
    isBoundedAbove : ∃ x ∈ S, ∀ y ∈ S, y ≤ x

  noncomputable abbrev max {α : Type _} [PartialOrder α] (S : Set α) (wd : max.WD S) : α :=
    Classical.choose wd.isBoundedAbove

  structure card.WD {α : Type _} (S : Set α) : Prop where
    isFinite : S.Finite

  noncomputable abbrev card {α : Type _} (S : Set α) (wd : card.WD S) : ℤ :=
    have : Fintype S := @Fintype.ofFinite _ wd.isFinite
    S.toFinset.card

  section Lemmas

    theorem min.def {α : Type _} [PartialOrder α] {S : Set α} (wd : min.WD S) :
        ∀ y ∈ S, min S wd ≤ y :=
      Classical.choose_spec wd.isBoundedBelow |>.2

    theorem max.def {α : Type _} [PartialOrder α] {S : Set α} (wd : max.WD S) :
        ∀ y ∈ S, y ≤ max S wd :=
      Classical.choose_spec wd.isBoundedAbove |>.2

    @[grind =, simp]
    theorem NAT.eq_interval : NAT = (0 .. MAXINT) := rfl

    @[grind =, simp]
    theorem NAT₁.eq_interval : NAT₁ = (1 .. MAXINT) := rfl

    @[grind =, simp]
    theorem INT.eq_interval : INT = (MININT .. MAXINT) := rfl

    @[grind =, simp]
    theorem NATURAL.mem_iff (n : Int) : n ∈ NATURAL ↔ 0 ≤ n := by
      rw [NATURAL, Set.mem_setOf_eq]

    @[grind =, simp]
    theorem NATURAL₁.mem_iff (n : Int) : n ∈ NATURAL₁ ↔ 1 ≤ n := by
      rw [NATURAL₁, Set.mem_setOf_eq]

    @[grind =, simp]
    theorem INTEGER.mem_iff (n : Int) : n ∈ INTEGER ↔ True := Iff.rfl

    @[grind =, simp]
    theorem NAT.mem_iff (n : Int) : n ∈ NAT ↔ 0 ≤ n ∧ n ≤ MAXINT := by
      rw [NAT, Set.mem_setOf_eq]

    @[grind =, simp]
    theorem NAT₁.mem_iff (n : Int) : n ∈ NAT₁ ↔ 1 ≤ n ∧ n ≤ MAXINT := by
      rw [NAT₁, Set.mem_setOf_eq]

    @[grind =, simp]
    theorem INT.mem_iff (n : Int) : n ∈ INT ↔ MININT ≤ n ∧ n ≤ MAXINT := by
      rw [INT, Set.mem_setOf_eq]

    @[grind =, simp]
    theorem interval.mem_iff {lo hi : ℤ} (z : ℤ) : z ∈ (lo .. hi) ↔ lo ≤ z ∧ z ≤ hi :=
      Set.mem_Icc

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

    @[grind =]
    theorem interval.empty_eq {lo hi : ℤ} (h : hi < lo) : (lo .. hi) = ∅ := by
      ext z
      constructor
      · rintro ⟨_, _⟩
        grind only
      · intro hfalse
        grind only [= Set.mem_Icc, = Set.mem_empty_iff_false]


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

    @[grind., simp, wd_min]
    theorem min.WD_NATURAL : min.WD NATURAL := by
      exists 0
      and_intros
      · rw [Builtins.NATURAL, Set.mem_setOf]
      · intro y hy
        rwa [Set.mem_setOf] at hy

    @[wd_min]
    theorem min.WD_of_finite {α : Type _} [LinearOrder α] {S A : Set α} (h : S ∈ FIN₁ A) :
        min.WD S := by
      let fin := Set.Finite.to_subtype h.1.2
      let nemp := Set.Nonempty.to_subtype h.2
      obtain ⟨x, h⟩ := Finite.exists_min (@_root_.id ↑S)
      exact ⟨x, Subtype.coe_prop x, fun y hy ↦ h ⟨y, hy⟩⟩

    @[wd_max]
    theorem max.WD_of_finite {α : Type _} [LinearOrder α] {S A : Set α} (h : S ∈ FIN₁ A) :
        max.WD S := by
      let fin := Set.Finite.to_subtype h.1.2
      let nemp := Set.Nonempty.to_subtype h.2
      obtain ⟨x, h⟩ := Finite.exists_max (@_root_.id ↑S)
      exact ⟨x, Subtype.coe_prop x, fun y hy ↦ h ⟨y, hy⟩⟩

    @[grind ., wd_max]
    theorem max.WD_interval {lo hi : ℤ} (h : lo ≤ hi) : max.WD (lo..hi) := by
      exists hi
      and_intros <;> grind

    @[grind ., wd_min]
    theorem min.WD_interval {lo hi : ℤ} (h : lo ≤ hi) : min.WD (lo..hi) := by
      exists lo
      and_intros <;> grind

    @[grind →]
    theorem min.mem {α : Type _} [PartialOrder α] {S : Set α} (wd : min.WD S) :
        min S wd ∈ S := (Classical.choose_spec wd.isBoundedBelow).1

    @[grind →]
    theorem max.mem {α : Type _} [PartialOrder α] {S : Set α} (wd : max.WD S) :
        max S wd ∈ S := (Classical.choose_spec wd.isBoundedAbove).1

    @[grind ., wd_min]
    theorem min.WD_of_union {α : Type _} [LinearOrder α] {S T : Set α}
        (hS : min.WD S) (hT : min.WD T) : min.WD (S ∪ T) := by
      obtain ⟨s_min, s_min_mem, s_min_bnd⟩ := hS
      obtain ⟨t_min, t_min_mem, t_min_bnd⟩ := hT
      let m := if s_min ≤ t_min then s_min else t_min
      exists m
      and_intros
      · unfold m
        split_ifs with hm
        · exact Set.mem_union_left T s_min_mem
        · exact Set.mem_union_right S t_min_mem
      · rintro y (hy | hy)
        · unfold m
          split_ifs with hm
          · exact s_min_bnd y hy
          · exact le_trans (le_of_not_ge hm) (s_min_bnd y hy)
        · unfold m
          split_ifs with hm
          · exact le_trans hm (t_min_bnd y hy)
          · exact t_min_bnd y hy

    @[grind ., wd_max]
    theorem max.WD_of_union {α : Type _} [LinearOrder α] {S T : Set α}
        (hS : max.WD S) (hT : max.WD T) : max.WD (S ∪ T) := by
      obtain ⟨s_max, s_max_mem, s_max_bnd⟩ := hS
      obtain ⟨t_max, t_max_mem, t_max_bnd⟩ := hT
      let m := if t_max ≤ s_max then s_max else t_max
      exists m
      and_intros
      · unfold m
        split_ifs with hm
        · exact Set.mem_union_left T s_max_mem
        · exact Set.mem_union_right S t_max_mem
      · rintro y (hy | hy)
        · unfold m
          split_ifs with hm
          · exact s_max_bnd y hy
          · exact le_trans
              (le_trans (s_max_bnd y hy) (le_of_not_ge hm))
              (t_max_bnd t_max t_max_mem)
        · unfold m
          split_ifs with hm
          · exact le_trans (t_max_bnd y hy) hm
          · exact t_max_bnd y hy

    @[grind ., simp]
    theorem interval.min_eq {lo hi : Int} (h : lo ≤ hi) :
        min (lo .. hi) (min.WD_interval h) = lo := by
      unfold min
      generalize_proofs hm
      obtain ⟨m_def, m_is_min⟩ := Classical.choose_spec hm
      exact le_antisymm (m_is_min _ (Set.left_mem_Icc.mpr h)) m_def.1

    @[grind ., simp]
    theorem interval.max_eq {lo hi : Int} (h : lo ≤ hi) :
        max (lo .. hi) (max.WD_interval h) = hi := by
      unfold max
      generalize_proofs hm
      obtain ⟨m_def, m_is_max⟩ := Classical.choose_spec hm
      exact le_antisymm m_def.2 (m_is_max _ (Set.right_mem_Icc.mpr h))

    @[grind ., wd_min]
    theorem min.WD_singleton {α : Type _} [PartialOrder α] {a : α} : min.WD {a} :=
      ⟨a, Set.mem_singleton a, fun _ ↦ ge_of_eq⟩

    @[grind ., wd_max]
    theorem max.WD_singleton {α : Type _} [PartialOrder α] {a : α} : max.WD {a} :=
      ⟨a, Set.mem_singleton a, fun _ ↦ le_of_eq⟩

    @[simp]
    theorem min.of_singleton {α : Type _} [PartialOrder α] {a : α} :
        min {a} (min.WD_singleton) = a := by
      unfold min
      generalize_proofs ha
      exact (Classical.choose_spec ha).1

    @[grind ., wd_min]
    theorem min.WD_of_insert {α : Type _} [LinearOrder α] {S : Set α} (a : α)
        (hS : min.WD S) : min.WD (insert a S) := by
      obtain ⟨s_min, s_min_mem, s_min_bnd⟩ := hS
      let m := if a ≤ s_min then a else s_min
      exists m
      unfold m
      split_ifs with hm
      · and_intros
        · exact Set.mem_insert a S
        · intro y hy
          rw [Set.mem_insert_iff] at hy
          obtain rfl | hy := hy
          · exact le_refl y
          · exact le_trans hm (s_min_bnd y hy)
      · and_intros
        · exact Set.mem_insert_of_mem a s_min_mem
        · intro y hy
          rw [Set.mem_insert_iff] at hy
          obtain rfl | hy := hy
          · exact le_of_not_ge hm
          · exact s_min_bnd y hy

    @[grind ., simp]
    theorem min.of_insert {α : Type _} [LinearOrder α] {S : Set α} (a : α)
        (hS : min.WD S) :
        min (insert a S) (min.WD_of_insert a hS) =
          if a ≤ min S hS then a else min S hS := by
      unfold min
      split_ifs with ha
      · generalize_proofs h₁ h₂ at ha ⊢
        obtain ⟨m_def, m_is_min⟩ := Classical.choose_spec h₂
        obtain ⟨s_min_def, s_min_is_min⟩ := Classical.choose_spec h₁
        set m := choose h₂
        set s_min := choose h₁
        rw [Set.mem_insert_iff] at m_def
        obtain m_eq | m_in := m_def
        · exact m_eq
        · apply le_antisymm
            (m_is_min _ (Set.mem_insert a S))
            (le_trans ha (s_min_is_min m m_in))
      · generalize_proofs h₁ h₂
        obtain ⟨m_def, m_is_min⟩ := Classical.choose_spec h₂
        obtain ⟨s_min_def, s_min_is_min⟩ := Classical.choose_spec h₁
        set m := choose h₂
        set s_min := choose h₁
        rw [Set.mem_insert_iff] at s_min_def
        obtain s_min_eq | s_min_in := s_min_def
        · rw [←s_min_eq] at ha
          rw [not_le] at ha
          simp at s_min_is_min
          nomatch lt_irrefl _ (lt_of_le_of_lt (s_min_is_min.2 m m_def) ha)
        · apply le_antisymm
            (s_min_is_min _ (Set.mem_insert_of_mem a m_def))
            (m_is_min s_min s_min_in)

    @[grind ., wd_max]
    theorem max.WD_of_insert {α : Type _} [LinearOrder α] {S : Set α} (a : α)
        (hS : max.WD S) : max.WD (insert a S) := by
      obtain ⟨s_max, s_max_mem, s_max_bnd⟩ := hS
      let m := if s_max ≤ a then a else s_max
      exists m
      unfold m
      split_ifs with hm
      · and_intros
        · exact Set.mem_insert a S
        · intro y hy
          rw [Set.mem_insert_iff] at hy
          obtain rfl | hy := hy
          · exact le_refl y
          · exact le_trans (s_max_bnd y hy) hm
      · and_intros
        · exact Set.mem_insert_of_mem a s_max_mem
        · intro y hy
          rw [Set.mem_insert_iff] at hy
          obtain rfl | hy := hy
          · exact le_of_not_ge hm
          · exact s_max_bnd y hy

    @[grind ., simp]
    theorem max.of_insert {α : Type _} [LinearOrder α] {S : Set α} (a : α)
        (hS : max.WD S) :
        max (insert a S) (max.WD_of_insert a hS) =
          if max S hS ≤ a then a else max S hS := by
      unfold max
      split_ifs with ha
      · generalize_proofs h₁ h₂ at ha ⊢
        obtain ⟨m_def, m_is_max⟩ := Classical.choose_spec h₂
        obtain ⟨s_max_def, s_max_is_max⟩ := Classical.choose_spec h₁
        set m := choose h₂
        set s_max := choose h₁
        rw [Set.mem_insert_iff] at m_def
        obtain m_eq | m_in := m_def
        · exact m_eq
        · apply le_antisymm
            (le_trans (s_max_is_max m m_in) ha)
            (m_is_max _ (Set.mem_insert a S))
      · generalize_proofs h₁ h₂
        obtain ⟨m_def, m_is_max⟩ := Classical.choose_spec h₂
        obtain ⟨s_max_def, s_max_is_max⟩ := Classical.choose_spec h₁
        set m := choose h₂
        set s_max := choose h₁
        rw [Set.mem_insert_iff] at s_max_def
        obtain s_max_eq | s_max_in := s_max_def
        · rw [←s_max_eq] at ha
          rw [not_le] at ha
          simp at s_max_is_max
          nomatch lt_irrefl _ (lt_of_le_of_lt (s_max_is_max.2 m m_def) ha)
        · apply le_antisymm
            (m_is_max s_max s_max_in)
            (s_max_is_max _ (Set.mem_insert_of_mem a m_def))

    @[simp]
    theorem max.of_singleton {α : Type _} [PartialOrder α] {a : α} :
        max {a} (max.WD_singleton) = a := by
      unfold max
      generalize_proofs ha
      exact (Classical.choose_spec ha).1

    @[grind .]
    theorem max.ge_min {α : Type _} [PartialOrder α] {S : Set α}
        (hmax : max.WD S) (hmin : min.WD S) :
        max S hmax ≥ min S hmin := by
      unfold max min
      generalize_proofs hmax hmin
      obtain ⟨-, is_max⟩ := Classical.choose_spec hmax
      obtain ⟨min_def, -⟩ := Classical.choose_spec hmin
      exact is_max (choose hmin) min_def

    @[grind .]
    theorem min.le_max {α : Type _} [PartialOrder α] {S : Set α}
      (hmin : min.WD S) (hmax : max.WD S) :
        min S hmin ≤ max S hmax := max.ge_min hmax hmin

    @[wd_min]
    theorem min.WD_of_finite_image_pfun {α β : Type _} [LinearOrder β] {A : Set α } {B : Set β}
      {f : SetRel α β} {S : Set α} (hf : f ∈ A ⇸ B) (hS : S ∈ FIN₁ (dom f)) :
        min.WD (f[S]) := by
      apply min.WD_of_finite (A := f[S])
      and_intros
      · exact subset_refl _
      · obtain ⟨⟨Sdom, Sfin⟩, Snemp⟩ := hS
        let S' := Set.Finite.toFinset Sfin
        suffices f[S'].Finite by
          apply Set.Finite.subset this
          intro x hx
          obtain ⟨w, wS, wxf⟩ := hx
          exists w, ?_
          · simpa [S']
          · exact wxf
        induction S' using Finset.induction with
        | empty => simp only [Finset.coe_empty, SetRel.image_empty_right, Set.finite_empty]
        | insert x S notMem IH =>
          have : f[insert x S] = f[{x}] ∪ f[S] := by ext; simp
          simp only [Finset.coe_insert, this, Set.finite_union]
          and_intros
          · by_cases hx : x ∈ dom f
            · obtain ⟨y, hy⟩ := hx
              have : f[{x}] = {y} := by
                ext z
                simp only [SetRel.image, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
                constructor
                · exact (hf.2 · hy)
                · rintro rfl
                  exact hy
              rw [this]
              exact Set.finite_singleton y
            · have : f[{x}] = ∅ := by
                ext z
                simp only [SetRel.image, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq,
                  Set.mem_empty_iff_false, iff_false]
                exact fun contr ↦ nomatch hx ⟨z, contr⟩
              rw [this]
              exact Set.finite_empty
          · exact IH
      · obtain ⟨⟨sub_dom, _⟩, s, hs⟩ := hS
        obtain ⟨w, hw⟩ := sub_dom hs
        exists w, s

    @[wd_min]
    theorem min.WD_of_finite_image_tfun {α β : Type _} [LinearOrder β] {A : Set α } {B : Set β}
      {f : SetRel α β} {S : Set α} (hf : f ∈ A ⟶ B) (hS : S ∈ FIN₁ A) :
        min.WD (f[S]) := by
      apply min.WD_of_finite_image_pfun (Set.mem_of_mem_inter_left hf)
      rwa [tfun_dom_eq hf]

    @[wd_max]
    theorem max.WD_of_finite_image_pfun {α β : Type _} [LinearOrder β] {A : Set α } {B : Set β}
      {f : SetRel α β} {S : Set α} (hf : f ∈ A ⇸ B) (hS : S ∈ FIN₁ (dom f)) :
        max.WD (f[S]) := by
      apply max.WD_of_finite (A := f[S])
      and_intros
      · exact subset_refl _
      · obtain ⟨⟨Sdom, Sfin⟩, Snemp⟩ := hS
        let S' := Set.Finite.toFinset Sfin
        suffices f[S'].Finite by
          apply Set.Finite.subset this
          intro x hx
          obtain ⟨w, wS, wxf⟩ := hx
          exists w, ?_
          · simpa [S']
          · exact wxf
        induction S' using Finset.induction with
        | empty => simp only [Finset.coe_empty, SetRel.image_empty_right, Set.finite_empty]
        | insert x S notMem IH =>
          have : f[insert x S] = f[{x}] ∪ f[S] := by ext; simp
          simp only [Finset.coe_insert, this, Set.finite_union]
          and_intros
          · by_cases hx : x ∈ dom f
            · obtain ⟨y, hy⟩ := hx
              have : f[{x}] = {y} := by
                ext z
                simp only [SetRel.image, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
                constructor
                · exact (hf.2 · hy)
                · rintro rfl
                  exact hy
              rw [this]
              exact Set.finite_singleton y
            · have : f[{x}] = ∅ := by
                ext z
                simp only [SetRel.image, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq,
                  Set.mem_empty_iff_false, iff_false]
                exact fun contr ↦ nomatch hx ⟨z, contr⟩
              rw [this]
              exact Set.finite_empty
          · exact IH
      · obtain ⟨⟨sub_dom, _⟩, s, hs⟩ := hS
        obtain ⟨w, hw⟩ := sub_dom hs
        exists w, s

    @[wd_max]
    theorem max.WD_of_finite_image_tfun {α β : Type _} [LinearOrder β] {A : Set α } {B : Set β}
      {f : SetRel α β} {S : Set α} (hf : f ∈ A ⟶ B) (hS : S ∈ FIN₁ A) :
        max.WD (f[S]) := by
      apply max.WD_of_finite_image_pfun (Set.mem_of_mem_inter_left hf)
      rwa [tfun_dom_eq hf]

    @[grind .]
    theorem min.mono {α : Type _} [PartialOrder α] {S T : Set α} (hsub : T ⊆ S)
      (hS : min.WD S) (hT : min.WD T) : min S hS ≤ min T hT :=
        (choose_spec hS.isBoundedBelow).right
          (choose hT.isBoundedBelow)
          (hsub (choose_spec hT.isBoundedBelow).left)

    @[grind .]
    theorem max.mono {α : Type _} [PartialOrder α] {S T : Set α} (hsub : S ⊆ T)
      (hS : max.WD S) (hT : max.WD T) : max S hS ≤ max T hT :=
        (choose_spec hT.isBoundedAbove).right
          (choose hS.isBoundedAbove)
          (hsub (choose_spec hS.isBoundedAbove).left)

    @[grind ., simp, wd_card]
    theorem card.WD_of_empty {α : Type _} : card.WD (∅ : Set α) where
      isFinite := Set.finite_empty

    @[grind ., simp, wd_card]
    theorem card.WD_of_interval {lo hi : ℤ} : card.WD (lo .. hi) where
      isFinite := interval.finite lo hi

    @[grind ., simp]
    theorem card.of_empty {α : Type _} : card (∅ : Set α) (card.WD_of_empty) = 0 := by
      simp only [card, Set.toFinset_empty, Finset.card_empty, Nat.cast_zero]

    @[grind =_, simp]
    theorem card.of_interval {lo hi : ℤ} :
        card (lo .. hi) (card.WD_of_interval) = Max.max (hi + 1 - lo) 0 := by
      simp only [card, Set.toFinset_Icc, Int.card_Icc, Int.ofNat_toNat]

    @[grind =_, simp]
    theorem card.of_interval' {lo hi : ℤ} (h : lo ≤ hi) :
        card (lo .. hi) (card.WD_of_interval) = hi - lo + 1 := by
      simp only [of_interval]
      rw [Int.max_eq_left]
      · symm
        exact sub_add_eq_add_sub hi lo 1
      · rw [Int.sub_nonneg]
        exact Int.le_add_one h

    @[grind <=, wd_card]
    theorem card.WD_of_subset {α : Type _} {S T : Set α} (hS : S ⊆ T)
        (hT : card.WD T) : card.WD S where
      isFinite := Set.Finite.subset hT.isFinite hS

    @[wd_card]
    theorem card.WD_of_finite {α : Type _} {S A : Set α} (h : S ∈ FIN A) :
        card.WD S where
      isFinite := h.2

    @[wd_card]
    theorem card.WD_of_finite' {α : Type _} {S A : Set α} (h : S ∈ FIN₁ A) :
        card.WD S where
      isFinite := h.1.2

    @[grind ., wd_card]
    theorem card.WD_of_singleton {α : Type _} {a : α} : card.WD {a} where
      isFinite := Set.finite_singleton a

    @[simp]
    theorem card.of_singleton {α : Type _} {a : α} :
        card {a} WD_of_singleton = 1 := by
      simp only [card, Set.toFinset_singleton, Finset.card_singleton, Nat.cast_one]

    @[mono]
    theorem card.mono {α : Type _} {S T : Set α} (hS : S ⊆ T) (hT : card.WD T) :
        card S (card.WD_of_subset hS hT) ≤ card T hT := by
      rw [Int.ofNat_le]
      apply Finset.card_le_card
      have : Finite ↑S := (card.WD_of_subset hS hT).isFinite
      have : Finite ↑T := hT.isFinite
      exact @Set.toFinset_mono α S T (Fintype.ofFinite ↑S) (Fintype.ofFinite ↑T) hS

    @[grind ., wd_card]
    theorem card.WD_of_inter {α : Type _} {S T : Set α} (h : card.WD S ∨ card.WD T) :
        card.WD (S ∩ T) where
      isFinite := by
        rcases h with hS | hT
        · exact Set.Finite.inter_of_left hS.isFinite _
        · exact Set.Finite.inter_of_right hT.isFinite _

    @[grind ., wd_card]
    theorem card.WD_of_union {α : Type _} {S T : Set α} (hS : card.WD S) (hT : card.WD T) :
        card.WD (S ∪ T) where
      isFinite := Set.Finite.union hS.isFinite hT.isFinite

    @[grind ., wd_card]
    theorem card.WD_of_insert {α : Type _} {S : Set α} (a : α)
        (hS : card.WD S) : card.WD (insert a S) where
      isFinite := Set.Finite.insert a hS.isFinite

    @[grind ., wd_card]
    theorem card.WD_of_insert' {α : Type _} {S : Set α} (a : α)
        (hS : card.WD S) : card.WD (S ∪ {a}) where
      isFinite := by simpa only [Set.union_singleton, Set.finite_insert] using hS.isFinite

    @[grind ., simp]
    theorem card.of_insert {α : Type _} {S : Set α} (a : α)  (hS : card.WD S) :
        card (insert a S) (card.WD_of_insert a hS) =
          if a ∈ S then card S hS else card S hS + 1 := by
      split_ifs with ha
      · conv =>
          enter [1,1]
          rw [Set.insert_eq_of_mem ha]
      · unfold card
        extract_lets h₁ h₂
        simp only [Set.toFinset_insert, Set.toFinset_card]
        rw [Finset.card_insert_eq_ite, ite_cond_eq_false _ _ (eq_false ?_)]
        · simp only [Set.toFinset_card, Nat.cast_add, Nat.cast_one]
        · rwa [Set.mem_toFinset]

    @[grind ., wd_card]
    theorem card.WD_of_sdiff {α : Type _} {S T : Set α} (hS : card.WD S) : card.WD (S \ T) where
      isFinite := Set.Finite.sdiff hS.isFinite

    @[simp]
    theorem card.of_sdiff {α : Type _} {S T : Set α} (hS : card.WD S) :
        card (S \ T) (card.WD_of_sdiff hS) =
          card S hS - card (S ∩ T) (WD_of_inter (Or.inl hS)) := by
      simp only [card]
      rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card',
        ← Set.ncard_eq_toFinset_card']
      have hSfin : S.Finite := hS.isFinite
      have key : ((S \ T) ∪ (S ∩ T)) = S := by
        ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
      have hdisj : Disjoint (S \ T) (S ∩ T) := by
        rw [Set.disjoint_left]; rintro x ⟨_, hxT⟩ ⟨_, hxT'⟩; exact hxT hxT'
      have hu := Set.ncard_union_eq hdisj hSfin.sdiff (hSfin.inter_of_left _)
      rw [key] at hu
      omega

    @[simp]
    theorem card.of_diff_singleton {α : Type _} {S : Set α} (a : α) (hS : card.WD S) :
        card (S \ {a}) (card.WD_of_sdiff hS) =
          if a ∈ S then card S hS - 1 else card S hS := by
      rw [card.of_sdiff hS]
      split_ifs with ha
      · have : S ∩ {a} = {a} := by
          ext
          simp
          rintro rfl
          assumption
        simp only [this, of_singleton]
      · have : S ∩ {a} = ∅ := by
          ext
          simp
          rintro _ rfl
          contradiction
        simp only [this, of_empty, sub_zero]

  end Lemmas

  private theorem min.WD_iff_AtelierB_WD {S : Set ℤ} :
      min.WD S ↔ S ≠ ∅ ∧ S ∩ (INTEGER \ NATURAL) ∈ FIN INTEGER where
    mp := by
      rintro ⟨m, m_in_S, m_is_lb⟩
      and_intros
      · exact ne_of_mem_of_not_mem' m_in_S _root_.id
      · exact fun _ _ => trivial
      · have hsubset : S ∩ (INTEGER \ NATURAL) ⊆ Set.Icc m (0 : ℤ) :=
          fun x ⟨hxS, _, hx_not_nat⟩ ↦ ⟨m_is_lb x hxS, le_of_lt (lt_of_not_ge hx_not_nat)⟩
        exact (Set.finite_Icc m 0).subset hsubset
    mpr := by
      rintro ⟨S_nemp, hS⟩
      by_cases hNemp : (S ∩ (INTEGER \ NATURAL)).Nonempty
      · have wd : min.WD (S ∩ (INTEGER \ NATURAL)) := by
          set T := S ∩ (INTEGER \ NATURAL)
          have _ := hS.2.to_subtype
          have _ : Nonempty (↑T) := hNemp.to_subtype
          obtain ⟨⟨x, hx⟩, hxmin⟩ := Finite.exists_min (@_root_.id (↑T))
          refine ⟨x, hx, ?_⟩
          intro y hy
          exact hxmin ⟨y, hy⟩

        have m_def := min.mem wd
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, Set.mem_setOf_eq, not_le,
          true_and] at m_def
        set m := min (S ∩ (INTEGER \ NATURAL)) wd
        refine ⟨m, m_def.1, ?_⟩
        intro y hy
        obtain lt_zero | ge_zero := Int.lt_or_le y 0
        · apply min.def wd y ⟨hy, trivial, ?_⟩
          rwa [Set.mem_setOf_eq, not_le]
        · exact le_trans (Int.le_of_lt m_def.right) ge_zero
      · simp only [Set.nonempty_def, not_exists, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ,
          Set.mem_setOf_eq, not_le, true_and, not_and, not_lt] at hNemp
        obtain ⟨a, haS⟩ := Set.nonempty_iff_ne_empty.2 S_nemp
        have ha0 := hNemp a haS
        have hex : ∃ n : ℕ, (n : ℤ) ∈ S := by
          use Int.toNat a
          rwa [Int.ofNat_toNat, Int.max_eq_left (hNemp a haS)]
        let n0 : ℕ := Nat.find hex
        have hn0 : (n0 : ℤ) ∈ S := Nat.find_spec hex
        refine ⟨(n0 : ℤ), hn0, ?_⟩
        · intro y hyS
          have hy0 : (0 : ℤ) ≤ y := hNemp y hyS
          have hpy : ↑(Int.toNat y) ∈ S := by
            rwa [Int.ofNat_toNat, Int.max_eq_left hy0]
          have : (n0 : ℤ) ≤ (Int.toNat y : ℤ) := (Int.ofNat_le).2 (Nat.find_min' hex hpy)
          rw [←Int.le_toNat (hNemp y hyS)]
          exact Nat.find_le hpy

  private theorem max.WD_iff_AtelierB_WD {S : Set ℤ} :
      max.WD S ↔ S ≠ ∅ ∧ S ∩ NATURAL ∈ FIN INTEGER where
    mp := by
      rintro ⟨m, m_in_S, m_is_lb⟩
      and_intros
      · exact ne_of_mem_of_not_mem' m_in_S _root_.id
      · exact fun _ _ => trivial
      · have hsubset : S ∩ NATURAL ⊆ Set.Icc (0 : ℤ) m :=
          fun x ⟨hxS, hx_nat⟩ ↦ ⟨hx_nat, m_is_lb x hxS⟩
        exact (Set.finite_Icc 0 m).subset hsubset
    mpr := by
      rintro ⟨S_nemp, hS⟩
      by_cases hNemp : (S ∩ NATURAL).Nonempty
      · have wd : max.WD (S ∩ NATURAL) := by
          set T := S ∩ NATURAL
          have _ := hS.2.to_subtype
          have _ : Nonempty (↑T) := hNemp.to_subtype
          obtain ⟨⟨x, hx⟩, hxmin⟩ := Finite.exists_max (@_root_.id (↑T))
          refine ⟨x, hx, ?_⟩
          intro y hy
          exact hxmin ⟨y, hy⟩

        have m_def := max.mem wd
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at m_def
        set m := max (S ∩ NATURAL) wd
        refine ⟨m, m_def.1, ?_⟩
        intro y hy
        obtain lt_zero | ge_zero := Int.lt_or_le y 0
        · exact le_trans (le_of_lt lt_zero) m_def.2
        · apply max.def wd y ⟨hy, ?_⟩
          rwa [Set.mem_setOf_eq]
      · simp only [Set.inter_nonempty_iff_exists_right, Set.mem_setOf_eq, not_exists,
          not_and] at hNemp
        refine { isBoundedAbove := ?_ }
        let T : Set ℤ := (fun z : ℤ => -z) '' S
        have T_nonempty : T.Nonempty := by
          obtain ⟨a, haS⟩ := Set.nonempty_iff_ne_empty.2 S_nemp
          exact ⟨-a, ⟨a, haS, rfl⟩⟩

        have T_nonneg : ∀ t ∈ T, (0 : ℤ) ≤ t := by
          intro t ht
          obtain ⟨y, hyS, rfl⟩ := ht
          have hy_not : ¬ (0 : ℤ) ≤ y := (hNemp y · hyS)
          simp only [Int.neg_nonneg, ge_iff_le]
          exact Int.le_of_not_le hy_not

        obtain ⟨m, hmT, hmMin⟩ : ∃ m ∈ T, ∀ z ∈ T, m ≤ z := by
          obtain ⟨aT, haT⟩ := T_nonempty
          have ha0 : (0 : ℤ) ≤ aT := T_nonneg aT haT

          have hex : ∃ n : ℕ, (n : ℤ) ∈ T := by
            use Int.toNat aT
            rwa [Int.ofNat_toNat, Int.max_eq_left ha0]

          let n0 : ℕ := Nat.find hex
          have hn0 : (n0 : ℤ) ∈ T := Nat.find_spec hex

          use (n0 : ℤ), hn0
          intro z hz
          have hz0 : (0 : ℤ) ≤ z := T_nonneg z hz
          have hpz : (Int.toNat z : ℤ) ∈ T := by
            rwa [Int.ofNat_toNat, Int.max_eq_left hz0]
          have hn0_le : n0 ≤ Int.toNat z := Nat.find_min' hex hpz
          have : (n0 : ℤ) ≤ (Int.toNat z : ℤ) := (Int.ofNat_le).2 hn0_le
          exact (Int.le_toNat (T_nonneg z hz)).mp hn0_le

        obtain ⟨x, hxS, hxEq⟩ := hmT
        use x, hxS
        intro y hyS
        have hm_le : m ≤ (-y : ℤ) := hmMin (-y) ⟨y, hyS, rfl⟩
        have := neg_le_neg (le_of_eq_of_le hxEq hm_le)
        rwa [neg_neg, neg_neg] at this

end B.Builtins
