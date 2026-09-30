import Barrel

open B.Builtins

namespace ZoneMonitorSupport

/-- Sensors with a recorded value that belong to the selected zone. -/
abbrev available {α β γ : Type*} (r : SetRel α β) (zone : SetRel α γ) (z : γ) : Set α :=
  dom r ∩ (zone⁻¹)[{z}]

@[simp]
theorem mem_available {α β γ : Type*} {r : SetRel α β} {zone : SetRel α γ}
    {z : γ} {s : α} : s ∈ available r zone z ↔ s ∈ dom r ∧ (s, z) ∈ zone := by
  simp [available]

theorem not_mem_update_of_unaffected {α β γ : Type*} {b : SetRel α β}
    {zone : SetRel α γ} {z : γ} (hz : z ∉ zone[dom b])
    {s : α} (hs : (s, z) ∈ zone) : s ∉ dom b := by
  intro hb
  exact hz ⟨s, hb, hs⟩

/-- Overriding readings does not change the available sensors in an unaffected zone. -/
theorem available_overload {α β γ : Type*} {r b : SetRel α β}
    {zone : SetRel α γ} {z : γ} (hz : z ∉ zone[dom b]) :
    available (r <+ b) zone z = available r zone z := by
  ext s
  simp only [mem_available, overload_dom_eq, Set.mem_union]
  constructor
  · rintro ⟨hr | hb, hs⟩
    · exact ⟨hr, hs⟩
    · exact (not_mem_update_of_unaffected hz hs hb).elim
  · rintro ⟨hr, hs⟩
    exact ⟨Or.inl hr, hs⟩

theorem overload_image_eq {α β : Type*} {r b : SetRel α β} {X : Set α}
    (hX : ∀ s ∈ X, s ∉ dom b) : (r <+ b)[X] = r[X] := by
  ext v
  constructor
  · rintro ⟨s, hs, hsr | hsb⟩
    · exact ⟨s, hs, hsr.1⟩
    · exact (hX s hs ⟨v, hsb⟩).elim
  · rintro ⟨s, hs, hsv⟩
    exact ⟨s, hs, Or.inl ⟨hsv, hX s hs⟩⟩

/-- Batch updates preserve all readings of a zone whose sensors were not updated. -/
theorem readings_overload {α β γ : Type*} {r b : SetRel α β}
    {zone : SetRel α γ} {z : γ} (hz : z ∉ zone[dom b]) :
    (r <+ b)[available (r <+ b) zone z] = r[available r zone z] := by
  rw [available_overload hz]
  exact overload_image_eq fun s hs =>
    not_mem_update_of_unaffected hz (mem_available.mp hs).2

theorem pfun_domSubtr {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    (hr : r ∈ S ⇸ D) (X : Set α) : (X ⩤ r) ∈ S ⇸ D := by
  exact ⟨fun _ h => hr.1 h.1, fun _ _ _ h₁ h₂ => hr.2 h₁.1 h₂.1⟩

theorem dom_domSubtr {α β : Type*} (r : SetRel α β) (X : Set α) :
    dom (X ⩤ r) = dom r \ X := by
  ext s
  simp only [dom, domSubtr, Set.mem_setOf_eq, Set.mem_sdiff]
  exact exists_and_right

theorem available_domSubtr {α β γ : Type*} {r : SetRel α β} {X : Set α}
    {zone : SetRel α γ} {z : γ} (hz : z ∉ zone[X]) :
    available (X ⩤ r) zone z = available r zone z := by
  ext s
  simp only [mem_available, dom_domSubtr, Set.mem_sdiff]
  constructor
  · exact fun ⟨⟨hs, _⟩, hsz⟩ => ⟨hs, hsz⟩
  · rintro ⟨hs, hsz⟩
    exact ⟨⟨hs, fun hX => hz ⟨s, hX, hsz⟩⟩, hsz⟩

theorem readings_domSubtr {α β γ : Type*} {r : SetRel α β} {X : Set α}
    {zone : SetRel α γ} {z : γ} (hz : z ∉ zone[X]) :
    (X ⩤ r)[available (X ⩤ r) zone z] = r[available r zone z] := by
  rw [available_domSubtr hz]
  ext v
  constructor
  · rintro ⟨s, hs, hsr, _⟩
    exact ⟨s, hs, hsr⟩
  · rintro ⟨s, hs, hsr⟩
    exact ⟨s, hs, hsr, fun hX => hz ⟨s, hX, (mem_available.mp hs).2⟩⟩

theorem available_finite {α β γ : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    (hr : r ∈ S ⇸ D) (hS : S.Finite) (zone : SetRel α γ) (z : γ) :
    (available r zone z).Finite :=
  hS.subset fun _ hs => pfun.dom_subset hr hs.1

theorem available_FIN₁ {α β γ : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    {zone : SetRel α γ} {z : γ} (hr : r ∈ S ⇸ D) (hS : S.Finite)
    (hne : available r zone z ≠ ∅) : available r zone z ∈ FIN₁ (dom r) :=
  ⟨⟨Set.inter_subset_left, available_finite hr hS zone z⟩,
    Set.nonempty_iff_ne_empty.mpr hne⟩

theorem card_WD_available {α β γ : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    (hr : r ∈ S ⇸ D) (hS : S.Finite) (zone : SetRel α γ) (z : γ) :
    card.WD (available r zone z) := ⟨available_finite hr hS zone z⟩

theorem min_WD_available {α β γ : Type*} [LinearOrder β] {r : SetRel α β}
    {S : Set α} {D : Set β} {zone : SetRel α γ} {z : γ}
    (hr : r ∈ S ⇸ D) (hS : S.Finite) (hne : available r zone z ≠ ∅) :
    min.WD (r[available r zone z]) :=
  min.WD_of_finite_image_pfun hr (available_FIN₁ hr hS hne)

theorem max_WD_available {α β γ : Type*} [LinearOrder β] {r : SetRel α β}
    {S : Set α} {D : Set β} {zone : SetRel α γ} {z : γ}
    (hr : r ∈ S ⇸ D) (hS : S.Finite) (hne : available r zone z ≠ ∅) :
    max.WD (r[available r zone z]) :=
  max.WD_of_finite_image_pfun hr (available_FIN₁ hr hS hne)

end ZoneMonitorSupport
