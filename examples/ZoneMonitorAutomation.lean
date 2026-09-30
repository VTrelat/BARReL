import examples.ZoneMonitorProofs

open B.Builtins

namespace ZoneMonitorSupport

theorem finite_of_FIN₁ {α : Type*} {S A : Set α} (h : S ∈ FIN₁ A) : S.Finite := h.1.2

theorem mem_source_of_dom {α β : Type*} {r : SetRel α β} {S : Set α} {D : Set β}
    {s : α} (hr : r ∈ S ⇸ D) (hs : s ∈ dom r) : s ∈ S := pfun.dom_subset hr hs

theorem mem_of_sdiff {α : Type*} {S T : Set α} {s : α} (hs : s ∈ S \ T) : s ∈ S := hs.1

theorem policy_nonempty {α β γ : Type*} {r : SetRel α β} {zone : SetRel α γ}
    {P : Set γ} {Q : ∀ z, z ∈ P → available r zone z ≠ ∅ → Prop}
    (h : ∀ z (hz : z ∈ P), (hne : available r zone z ≠ ∅) ∧' Q z hz hne)
    {z : γ} (hz : z ∈ P) : available r zone z ≠ ∅ := (h z hz).1

theorem policy_nonempty_union {α β γ : Type*} {r : SetRel α β} {zone : SetRel α γ}
    {P : Set γ} {Q : ∀ z, z ∈ P → available r zone z ≠ ∅ → Prop}
    (h : ∀ z (hz : z ∈ P), (hne : available r zone z ≠ ∅) ∧' Q z hz hne)
    {z x : γ} (hz : available r zone z ≠ ∅) (hx : x ∈ P ∪ {z}) :
    available r zone x ≠ ∅ := by
  rcases hx with hx | hx
  · exact policy_nonempty h hx
  · exact Set.mem_singleton_iff.mp hx ▸ hz

@[pfun]
theorem pfun_overload_same {α β : Type*} {S : Set α} {D : Set β} {r b : SetRel α β}
    (hr : r ∈ S ⇸ D) (hb : b ∈ S ⇸ D) : r <+ b ∈ S ⇸ D := by
  simpa only [Set.union_self] using pfun_of_overload hr hb

attribute [pfun] pfun_domSubtr
attribute [tfun] tfun_overload_singleton

macro "zone_pfun" : tactic => `(tactic| (first
  | assumption
  | (apply pfun_overload_same
     · assumption
     · first | assumption | (apply pfun_singleton <;> assumption))
  | (apply pfun_domSubtr; assumption)))

macro "zone_nonempty" : tactic => `(tactic|
  solve_by_elim (maxDepth := 4) only [*, policy_nonempty, policy_nonempty_union, mem_of_sdiff])

syntax "zone_wd" : tactic

open Lean Elab Tactic in
elab "zone_wd_guard" : tactic => do
  let target ← getMainTarget
  unless target.getAppFn.isConstOf ``card.WD ||
      target.getAppFn.isConstOf ``min.WD || target.getAppFn.isConstOf ``max.WD ||
      target.getAppFn.isConstOf ``app.WD do
    throwError "not a cardinality or extrema WD goal"

macro_rules
  | `(tactic| zone_wd) => `(tactic| (
      intros
      zone_wd_guard
      first
      | contradiction
      | (apply app.WD_of_mem_tfun
         · first | assumption | (apply tfun_overload_singleton <;> assumption)
         · solve_by_elim (maxDepth := 4) only [*, mem_source_of_dom,
             mem_of_sdiff, Set.mem_of_mem_of_subset])
      | (apply card_WD_available
         · zone_pfun
         · apply finite_of_FIN₁; assumption)
      | (apply min_WD_available
         · zone_pfun
         · apply finite_of_FIN₁; assumption
         · zone_nonempty)
      | (apply max_WD_available
         · zone_pfun
         · apply finite_of_FIN₁; assumption
         · zone_nonempty)))

macro_rules | `(tactic| barrel_solve) => `(tactic| zone_wd)

end ZoneMonitorSupport
