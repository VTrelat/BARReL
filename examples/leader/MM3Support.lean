import examples.leader.MM2Support

open B.Builtins

namespace Leader

/-- A constant relation is a total function on its first factor. -/
alias tfun_const_product := B.Builtins.tfun_const_product

/-- Updating one value within the domain and codomain preserves a total function. -/
alias tfun_override_singleton := B.Builtins.tfun_override_singleton

/-- The updated argument takes the new value. -/
theorem app_override_singleton_self {α β : Type*} {f : SetRel α β} {x : α} {y : β}
    (wd : app.WD (f <+ {(x, y)}) x) :
    app (f <+ {(x, y)}) x wd = y := by
  apply app.of_pair_eq
  exact Or.inr rfl

/-- All other arguments retain their value after a point update. -/
theorem app_override_singleton_of_ne {α β : Type*} {f : SetRel α β} {x a : α} {b : β}
    (hne : x ≠ a) (wd : app.WD (f <+ {(a, b)}) x) (oldwd : app.WD f x) :
    app (f <+ {(a, b)}) x wd = app f x oldwd := by
  apply app.of_pair_eq
  refine Or.inl ⟨app.pair_app_mem, ?_⟩
  simpa [dom] using hne

/-- A set-valued application is bounded exactly when its graph value is bounded. -/
theorem app_subset_iff {α β : Type*} {f : SetRel α (Set β)} {x : α} {s : Set β}
    (wd : app.WD f x) :
    app f x wd ⊆ s ↔ ∀ t, (x, t) ∈ f → t ⊆ s := by
  constructor
  · intro h t ht
    exact app.of_pair_eq wd ht ▸ h
  · intro h
    exact h _ app.pair_app_mem

/-- Membership in a set-valued application can be read directly from its graph. -/
theorem mem_app_iff {α β : Type*} {f : SetRel α (Set β)} {x : α} {y : β}
    (wd : app.WD f x) :
    y ∈ app f x wd ↔ ∃ t, (x, t) ∈ f ∧ y ∈ t := by
  constructor
  · intro h
    exact ⟨_, app.pair_app_mem, h⟩
  · rintro ⟨t, ht, hy⟩
    exact app.of_pair_eq wd ht ▸ hy

end Leader
