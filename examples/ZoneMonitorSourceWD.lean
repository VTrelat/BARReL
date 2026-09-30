import examples.ZoneMonitorSupport

open B.Builtins ZoneMonitorSupport

namespace ZoneMonitorSourceWD

theorem mem_dom_of_tfun {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    {x : α} (hr : r ∈ S ⟶ D) (hx : x ∈ S) : x ∈ dom r := by
  rw [tfun_dom_eq hr]
  exact hx

theorem pfun_own_dom_ran {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    (hr : r ∈ S ⇸ D) : r ∈ dom r ⇸ ran r :=
  (tfun.of_pfun hr).1

theorem mem_source_of_mem_dom {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    {x : α} (hr : r ∈ S ⇸ D) (hx : x ∈ dom r) : x ∈ S :=
  pfun.dom_subset hr hx

theorem available_FIN_self {α β γ : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    {zone : SetRel α γ} {z : γ} (hr : r ∈ S ⇸ D) (hS : S ∈ FIN₁ Set.univ) :
    available r zone z ∈ FIN (available r zone z) :=
  FIN.of_finite_self (available_finite hr hS.1.2 zone z)

/-- Every available sensor contributes a reading to the relational image. -/
theorem readings_ne_empty {α β γ : Type*} {r : SetRel α β}
    {zone : SetRel α γ} {z : γ} (hne : available r zone z ≠ ∅) :
    r[available r zone z] ≠ ∅ := by
  apply Set.Nonempty.ne_empty
  obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨v, hv⟩ := hs.1
  exact ⟨v, s, hs, hv⟩

theorem image_inter_FIN {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    (hr : r ∈ S ⇸ D) (hD : D.Finite) (X : Set α) (T : Set β) :
    r[X] ∩ T ∈ FIN T := by
  refine ⟨Set.inter_subset_right, hD.subset ?_⟩
  rintro v ⟨⟨s, _, hsr⟩, _⟩
  exact (hr.1 hsr).2

theorem image_inter_diff_FIN {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    (hr : r ∈ S ⇸ D) (hD : D.Finite) (X : Set α) (T U : Set β) :
    r[X] ∩ (T \ U) ∈ FIN T :=
  FIN.mono Set.sdiff_subset (image_inter_FIN hr hD X (T \ U))

end ZoneMonitorSourceWD
