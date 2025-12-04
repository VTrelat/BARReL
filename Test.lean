import Barrel.Discharger
import Mathlib.Util.AssertNoSorry

-- set_option trace.barrel true
-- set_option trace.barrel.cache true
-- set_option trace.barrel.wf true
-- set_option trace.barrel.checkpoints true
set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

mch_discharger "specs/Counter.mch"
next
  grind
next
  grind
next
  rintro x ⟨_, _⟩ _ _
  grind
next
  grind

mch_discharger "specs/Eval.mch"
next
  intros X Y _ _
  exists ∅, ∅, ∅
  exists ?_, ?_ <;> simp

mch_discharger "specs/Finite.mch"
next
  intros
  exact interval.FIN_mem

mch_discharger "specs/Nat.mch"
next
  rintro _ ⟨_, _⟩
  assumption

mch_discharger "specs/Collect.mch"
next
  simp

mch_discharger "specs/Forall.mch"
next
  rintro x1 x2 x3 ⟨⟨_, _⟩, _⟩ _
  assumption

mch_discharger "specs/Exists.mch"
next
  exists 0

-- -- -- TODO: fix
mch_discharger "specs/Injective.mch"
next
  rintro X Y F x y ⟨_, F_tot⟩ _ _ x_mem_X _
  exact app.WF_of_mem_tfun F_tot x_mem_X
next
  rintro X Y F x y ⟨_, F_tot⟩ _ _ _ y_mem_X
  exact app.WF_of_mem_tfun F_tot y_mem_X
next
  rintro X Y F x y ⟨⟨_, F_inj⟩, F_tot⟩ _ _ x_mem_X y_mem_X F_eq
  generalize_proofs wf_x wf_y at F_eq
  apply F_inj
  · exact app.pair_app_mem (wf := wf_x)
  · rw [F_eq]
    exact app.pair_app_mem (wf := wf_y)


-- -- -- TODO: fix
mch_discharger "specs/HO.mch"
next
  intros X Y x _ _  _ x_mem_X _ _ _ _ _ _ G G_fun
  exact app.WF_of_mem_tfun G_fun x_mem_X
next
  intros X Y x _ _ F x_mem_X _ _ _ F_fun _ _ _ _
  exact app.WF_of_mem_tfun F_fun x_mem_X
next
  intros X Y x y₀ y₁ F x_mem_X y₀_mem_Y y₁_mem_Y y₀_neq_y₁ F_fun _ _

  by_cases hF : (x, y₀) ∈ F
  · exists F <+ {(x, y₁)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₁} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · generalize_proofs _ wf_x
      rw [app.of_pair_iff wf_x] at hF
      simpa [hF, ←ne_eq, ne_comm, ne_eq]
  · exists F <+ {(x, y₀)}
    refine ⟨?_, ?_⟩
    · have X_eq : X = X ∪ {x} := by ext; grind
      have Y_eq : Y = Y ∪ {y₀} := by ext; grind
      rw [X_eq, Y_eq]
      exact tfun_of_overload F_fun tfun_of_singleton
    · generalize_proofs _ wf_x
      rw [app.of_pair_iff wf_x, ←ne_eq, ne_comm, ne_eq] at hF
      simpa

mch_discharger "specs/Demo.mch"
next
  exact fun _ => id
next
  intro s₀ hs₀
  apply FIN.of_inter
  left
  exact FIN.of_sub NAT.mem_FIN hs₀

-- -- -- TODO: fix
mch_discharger "specs/Extensionality.mch"
next
  intros X Y F _ _ _ F_fun _ x hx
  exact app.WF_of_mem_tfun F_fun hx
next
  intros X Y _ G _ _ _ G_fun x hx
  exact app.WF_of_mem_tfun G_fun hx
next
  intros X Y F G _ _ F_fun G_fun ext
  ext ⟨x, y⟩

  specialize ext x
  constructor <;> intro h
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq F_fun]
      exact mem_dom_of_pair_mem h

    specialize ext hx
    generalize_proofs wf_F wf_G at ext
    rw [app.of_pair_iff ‹_›] at h ⊢
    symm
    rwa [h] at ext
  · have hx : x ∈ X := by
      rw [←tfun_dom_eq G_fun]
      exact mem_dom_of_pair_mem h
    specialize ext hx
    generalize_proofs wf_F wf_G at ext
    rw [app.of_pair_iff ‹_›] at h ⊢
    rwa [h] at ext

mch_discharger "specs/CounterMin.mch"
next
  exact fun _ _ ↦ max.WF_singleton
next
  exact fun _ _ ↦ min.WF_singleton
next
  exact fun _ _ ↦ max.WF_of_finite
next
  exact fun _ _ ↦ min.WF_of_finite
next
  rintro _ z - - z_mem
  exact max.WF_interval <| neg_le_self z_mem
next
  rintro _ z - - z_mem
  exact min.WF_interval <| neg_le_self z_mem
next
  exact FIN₁.singleton_mem trivial
next
  intros _ _
  rw [max.of_singleton, min.of_singleton]
  rfl
next
  rintro X z - - z_mem
  exact interval.FIN₁_mem <| neg_le_self z_mem
next
  rintro X z - - hz
  rw [interval.min_eq (neg_le_self hz),
      interval.max_eq (neg_le_self hz),
      Int.neg_neg]

#check CounterMin.Initialisation_0
#check CounterMin.Initialisation_1
#check CounterMin.Operation_inc_2
#check CounterMin.Operation_inc_3

assert_no_sorry CounterMin.Initialisation_0
assert_no_sorry CounterMin.Initialisation_1
assert_no_sorry CounterMin.Operation_inc_2
assert_no_sorry CounterMin.Operation_inc_3

mch_discharger "specs/Pixels.mch"
next
  rintro Colors Red Green Blue pixels pixel pp hpixel rfl rfl Colors_card hpp ⟨x, y⟩ color _ h₁ h₂
  exact app.WF_of_mem_tfun hpp h₂
next
  rintro Colors Red Green Blue _ rfl rfl Colors_card
  and_intros
  · simp
  · intros x y z hxy hxz
    simp at hxy hxz
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hxy <;> {
      obtain ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ := hxz
      <;> rfl
    }
  · rintro x (rfl | rfl | rfl) <;> {
      exists 0
      simp
    }
next admit
next admit
next admit

mch_discharger "specs/Collect2.mch"
next
  grind
