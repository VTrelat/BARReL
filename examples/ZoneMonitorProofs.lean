import examples.ZoneMonitorSupport

open B.Builtins

namespace ZoneMonitorSupport

theorem tfun_overload_singleton {α β : Type*} {f : SetRel α β} {S : Set α} {D : Set β}
    {x : α} {v : β} (hf : f ∈ S ⟶ D) (hx : x ∈ S) (hv : v ∈ D) :
    f <+ {(x, v)} ∈ S ⟶ D := by
  simpa only [Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hx),
    Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hv)] using
    tfun_of_overload hf (tfun_of_singleton (a := x) (b := v))

theorem app_overload_singleton_self {α β : Type*} {f : SetRel α β} {x : α} {v : β}
    (wd : app.WD (f <+ {(x, v)}) x) : app (f <+ {(x, v)}) x wd = v := by
  apply app.of_pair_eq
  exact Or.inr (Set.mem_singleton _)

theorem app_overload_singleton_other {α β : Type*} {f : SetRel α β} {x s : α} {v : β}
    (hne : x ≠ s) (wd : app.WD f x) (wd' : app.WD (f <+ {(s, v)}) x) :
    app (f <+ {(s, v)}) x wd' = app f x wd := by
  apply app.of_pair_eq
  refine Or.inl ⟨app.pair_app_mem, ?_⟩
  rintro ⟨y, h⟩
  have he : (x, y) = (s, v) := Set.mem_singleton_iff.mp h
  exact hne (congrArg Prod.fst he)

theorem image_dom_singleton {α β γ : Type*} (zone : SetRel α γ) (s : α) (v : β)
    (wd : app.WD zone s) : zone[dom ({(s, v)} : SetRel α β)] = {app zone s wd} := by
  have hd : dom ({(s, v)} : SetRel α β) = {s} := by
    ext x
    simp [dom]
  rw [hd]
  exact app.image_singleton_eq_of_wd wd

end ZoneMonitorSupport
