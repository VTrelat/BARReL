import Barrel
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

import machine Falsehood from "specs"

next obligation of Falsehood by admit -- Literally `False`. Hopefully, unprovable in Lean
qed Falsehood

open B.Builtins

variable {α : Type}

def a : Set (Set ℤ) := {∅}

def X : Set (Set ℤ) := 𝒫₁ INTEGER

def y : Set (Set ℤ) := ∅

def GenPredicateX8 : Prop :=
  ∀ {α : Type} (a x : Set (Set α)) (y : ∀ {β : Type}, Set β),
    a ∉ 𝒫 x ∪ {y} → ∃ z, z ∈ a ∧ z ∉ x ∧ z ≠ y

def GenPredicateX8_fixed : Prop :=
  ∀ {α : Type} (a x : Set (Set α)) (y : ∀ {β : Type}, Set β),
    a ∉ 𝒫 (x ∪ {y}) → ∃ z, z ∈ a ∧ z ∉ x ∧ z ≠ y

theorem GenPredicateX8_unsound : ¬ GenPredicateX8 := by
  unfold GenPredicateX8
  intro GenPredicateX8
  specialize GenPredicateX8 a X ∅
  have derived_hypothesis_false :
      ¬ (∃ z : Set ℤ, z ∈ a ∧ z ∉ X ∧ z ≠ ∅) := by
    rintro ⟨z, hza, _, hzy⟩
    exact hzy hza
  absurd derived_hypothesis_false
  apply GenPredicateX8
  rintro (hsub | heq)
  · nomatch hsub (Set.mem_singleton ∅) |>.right
  · nomatch Set.singleton_ne_empty _ heq

theorem zero_eq_one_from_rule (rule : GenPredicateX8) : (0 : ℤ) = 1 :=
  absurd @rule GenPredicateX8_unsound

/-! ## The intended rule is sound

With the parentheses as intended, `not(a: POW(x \/ {y}))`, `y` is an element of the carrier of
`a`. The conclusion is then well typed and valid. This needs classical logic: from
`¬ ∀` one obtains `∃`. -/

theorem GenPredicateX8_fixed_sound : GenPredicateX8_fixed := by
  intro α a x y h
  by_contra! hne
  exact h fun z hz => or_iff_not_imp_left.mpr (hne z hz)
