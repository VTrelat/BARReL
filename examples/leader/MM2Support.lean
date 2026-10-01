import Barrel

open B.Builtins

namespace Leader

/-- Restricting a partial function preserves its typing and functionality. -/
lemma pfun_of_subset {α β : Type*} {A : Set α} {B : Set β} {f g : SetRel α β}
    (hf : f ∈ A ⇸ B) (hg : g ⊆ f) : g ∈ A ⇸ B := by
  exact ⟨hg.trans hf.1, fun {_ _ _} hxy hxz ↦ hf.2 (hg hxy) (hg hxz)⟩

/-- A fresh source node can be assigned a value without disturbing a partial function. -/
lemma pfun_union_singleton {α β : Type*} {A : Set α} {B : Set β} {f : SetRel α β}
    {x : α} {y : β} (hf : f ∈ A ⇸ B) (hx : x ∈ A) (hy : y ∈ B)
    (fresh : x ∉ dom f) : f ∪ {(x, y)} ∈ A ⇸ B := by
  constructor
  · exact Set.union_subset hf.1 (Set.singleton_subset_iff.mpr ⟨hx, hy⟩)
  · intro a b c hab hac
    rcases hab with hab | hab <;> rcases hac with hac | hac
    · exact hf.2 hab hac
    · rcases Set.mem_singleton_iff.mp hac with ⟨rfl, rfl⟩
      exact (fresh ⟨b, hab⟩).elim
    · rcases Set.mem_singleton_iff.mp hab with ⟨rfl, rfl⟩
      exact (fresh ⟨c, hac⟩).elim
    · exact (Prod.mk.inj (Set.mem_singleton_iff.mp hab)).2.trans
        (Prod.mk.inj (Set.mem_singleton_iff.mp hac)).2.symm

/-- A subrelation of a loop-free graph has no identity edges. -/
lemma inter_id_eq_empty_of_subset {α : Type*} {A : Set α} {g r : SetRel α α}
    (hg : B.Builtins.id A ∩ g = ∅) (hr : r ⊆ g) : r ∩ B.Builtins.id A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro edge hedge
  have : edge ∈ B.Builtins.id A ∩ g := ⟨hedge.2, hr hedge.1⟩
  simp [hg] at this

/-- Sending towards an unacknowledged neighbour cannot target an already attached node. -/
lemma send_target_unattached {α : Type*} {graph tree ack msg : SetRel α α} {x y : α}
    (symmetric : graph = graph⁻¹)
    (covered : dom tree ◁ (tree ∪ tree⁻¹) = dom tree ◁ graph)
    (tree_ack : tree ⊆ ack) (ack_msg : ack ⊆ msg)
    (edge : (x, y) ∈ graph) (unacknowledged : (y, x) ∉ ack)
    (fresh : x ∉ dom msg) : y ∉ dom tree := by
  intro attached
  have reverse : (y, x) ∈ graph := by
    rwa [symmetric, SetRel.mem_inv]
  have incident : (y, x) ∈ dom tree ◁ (tree ∪ tree⁻¹) := by
    rw [covered]
    exact ⟨reverse, attached⟩
  rcases incident.1 with outgoing | incoming
  · exact unacknowledged (tree_ack outgoing)
  · exact fresh ⟨y, ack_msg (tree_ack incoming)⟩

/-- An asymmetric relation stays asymmetric after adding an edge with no reverse or self-loop. -/
lemma asymmetric_union_singleton_of_no_reverse {α : Type*} {r : SetRel α α} {x y : α}
    (asymmetric : r ∩ r⁻¹ = ∅) (no_reverse : (y, x) ∉ r) (different : x ≠ y) :
    (r ∪ {(x, y)}) ∩ (r ∪ {(x, y)})⁻¹ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨a, b⟩ ⟨hab, hba⟩
  change (b, a) ∈ r ∪ {(x, y)} at hba
  rcases hab with hab | hab <;> rcases hba with hba | hba
  · have both : (a, b) ∈ r ∩ r⁻¹ := ⟨hab, hba⟩
    simp [asymmetric] at both
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hba
    exact no_reverse hab
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hab
    exact no_reverse hba
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp hab
    exact different (Prod.mk.inj (Set.mem_singleton_iff.mp hba)).1.symm

/-- Adding a message preserves the pairing of pending messages whose receiver has sent one. -/
lemma send_preserves_reciprocity {α : Type*} {graph tree ack msg : SetRel α α} {x y : α}
    (symmetric : graph = graph⁻¹) (tree_ack : tree ⊆ ack) (ack_msg : ack ⊆ msg)
    (msg_graph : msg ⊆ graph)
    (other_neighbors : ∀ a b, (a, b) ∈ msg → ∀ c ∈ graph[{a}], c ≠ b → (c, a) ∈ tree)
    (reciprocal : ∀ a b, (a, b) ∈ msg \ ack → b ∈ dom msg → (b, a) ∈ msg \ ack)
    (edge : (x, y) ∈ graph) (unacknowledged : (y, x) ∉ ack)
    (neighbors : graph[{x}] = (tree⁻¹)[{x}] ∪ {y}) (fresh : x ∉ dom msg)
    {a b : α} (pending : (a, b) ∈ (msg ∪ {(x, y)}) \ ack)
    (receiver : b ∈ dom (msg ∪ {(x, y)})) : (b, a) ∈ (msg ∪ {(x, y)}) \ ack := by
  rcases pending with ⟨old | new, not_ack⟩
  · obtain ⟨c, old_receiver | new_receiver⟩ := receiver
    · obtain ⟨reverse, reverse_pending⟩ := reciprocal a b ⟨old, not_ack⟩ ⟨c, old_receiver⟩
      exact ⟨Or.inl reverse, reverse_pending⟩
    · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp new_receiver
      have adjacent : a ∈ graph[{x}] := by
        have reverse : (x, a) ∈ graph := by
          rw [symmetric, SetRel.mem_inv]
          exact msg_graph old
        exact ⟨x, rfl, reverse⟩
      rw [neighbors] at adjacent
      rcases adjacent with attached | at_target
      · have attached_edge : (a, x) ∈ tree := by simpa using attached
        exact (not_ack (tree_ack attached_edge)).elim
      · have : a = y := Set.mem_singleton_iff.mp at_target
        subst a
        exact ⟨Or.inr rfl, fun hxy ↦ fresh ⟨y, ack_msg hxy⟩⟩
  · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp new
    obtain ⟨c, old_receiver | new_receiver⟩ := receiver
    · by_cases same : x = c
      · subst c
        exact ⟨Or.inl old_receiver, unacknowledged⟩
      · have adjacent : x ∈ graph[{y}] := by
          refine ⟨y, rfl, ?_⟩
          rwa [symmetric, SetRel.mem_inv]
        have attached := other_neighbors y c old_receiver x adjacent same
        exact (fresh ⟨y, ack_msg (tree_ack attached)⟩).elim
    · obtain ⟨rfl, rfl⟩ := Set.mem_singleton_iff.mp new_receiver
      exact ⟨Or.inr rfl, not_ack⟩

end Leader
