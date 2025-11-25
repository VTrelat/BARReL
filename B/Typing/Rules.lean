import B.Typing.Basic
import B.Syntax.Extra

open Batteries
namespace B

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ " x " : " τ:90 => Typing Γ x τ
-- local notation:90 Γ:90 " ⊩ " xs " : " τs:90 => Typing' Γ xs τs

inductive Typing : TypeContext → Term → BType → Prop where
  | var {Γ v τ} :
      Γ.find? v = some τ
    ----------------------
    → Γ ⊢ .var v : τ
  | int {Γ n} : Γ ⊢ .int n : .int
  | bool {Γ b} : Γ ⊢ .bool b : .bool
  | maplet {Γ α β x y}:
      Γ ⊢ x : α
    → Γ ⊢ y : β
    ----------------------------
    → Γ ⊢ x ↦ᴮ y : α ×ᴮ β
  | add {Γ x y} :
      Γ ⊢ x : .int
    → Γ ⊢ y : .int
    -------------------------
    → Γ ⊢ x +ᴮ y : .int
  | sub {Γ x y} :
      Γ ⊢ x : .int
    → Γ ⊢ y : .int
    -------------------------
    → Γ ⊢ x -ᴮ y : .int
  | mul {Γ x y} :
      Γ ⊢ x : .int
    → Γ ⊢ y : .int
    -------------------------
    → Γ ⊢ x *ᴮ y : .int
  | and {Γ x y} :
      Γ ⊢ x : .bool
    → Γ ⊢ y : .bool
    -------------------------
    → Γ ⊢ x ∧ᴮ y : .bool
  | or {Γ x y} :
      Γ ⊢ x : .bool
    → Γ ⊢ y : .bool
    -------------------------
    → Γ ⊢ x ∨ᴮ y : .bool
  | imp {Γ x y} :
      Γ ⊢ x : .bool
    → Γ ⊢ y : .bool
    -------------------------
    → Γ ⊢ x ⇒ᴮ y : .bool
  | not {Γ x} :
      Γ ⊢ x : .bool
    ------------------------
    → Γ ⊢ ¬ᴮ x : .bool
  | eq {Γ α x y} :
      Γ ⊢ x : α
    → Γ ⊢ y : α
    ------------------------
    → Γ ⊢ x =ᴮ y : .bool
  | le {Γ x y} :
      Γ ⊢ x : .int
    → Γ ⊢ y : .int
    ------------------------
    → Γ ⊢ x ≤ᴮ y : .bool
  | ℤ {Γ} : Γ ⊢ .ℤ : .set .int
  | 𝔹 {Γ} : Γ ⊢ .𝔹 : .set .bool
  | mem {Γ α x S}:
      Γ ⊢ x : α
    → Γ ⊢ S : .set α
    --------------------------
    → Γ ⊢ x ∈ᴮ S : .bool
  | collect {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} {D : List Term} {P : Term} :
      (vs_nemp : vs ≠ [])
    → (vs_nodup : vs.Nodup)
    → (vs_Γ_disj : ∀ v ∈ vs, v ∉ Γ)
    → (vs_αs_len : vs.length = αs.length)
    → (vs_D_len : vs.length = D.length)
    -- → (typD : ∀ i, Γ ⊢ D.get! i : αs.get! i)
    → (typD : List.Forall₂' D αs (λ Dᵢ αᵢ => Γ ⊢ Dᵢ : .set αᵢ) (vs_D_len ▸ vs_αs_len))
    → (typP : (vs.zipToAList αs ∪ Γ) ⊢ P : .bool) -- left-biased union
    --------------------------------------------------
    → Γ ⊢ .collect vs (D.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) P : .set (αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp))
  | pow {Γ α S}:
      Γ ⊢ S : .set α
    ---------------------------------
    → Γ ⊢ 𝒫ᴮ S : .set (.set α)
  | cprod {Γ α β S T}:
      Γ ⊢ S : .set α
    → Γ ⊢ T : .set β
    -----------------------------
    → Γ ⊢ S ⨯ᴮ T : .set (α ×ᴮ β)
  | union {Γ α S T}:
      Γ ⊢ S : .set α
    → Γ ⊢ T : .set α
    -----------------------------
    → Γ ⊢ S ∪ᴮ T : .set α
  | inter {Γ α S T}:
      Γ ⊢ S : .set α
    → Γ ⊢ T : .set α
    -----------------------------
    → Γ ⊢ S ∩ᴮ T : .set α
  | pfun {Γ α β S T}:
      Γ ⊢ S : .set α
    → Γ ⊢ T : .set β
    -----------------------------
    → Γ ⊢ S ⇸ᴮ T : .set (.set (α ×ᴮ β))
  | all {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} {D : List Term} {P : Term} :
      (vs_nemp : vs ≠ [])
    → (vs_nodup : vs.Nodup)
    → (vs_Γ_disj : ∀ v ∈ vs, v ∉ Γ)
    → (vs_αs_len : vs.length = αs.length)
    → (vs_D_len : vs.length = D.length)
    -- → (typD : ∀ i, Γ ⊢ D.get! i : αs.get! i)
    → (typD : List.Forall₂' D αs (λ Dᵢ αᵢ => Γ ⊢ Dᵢ : .set αᵢ) (vs_D_len ▸ vs_αs_len))
    → (typP : (vs.zipToAList αs ∪ Γ) ⊢ P : .bool) -- left-biased union
    --------------------------------------------------
    → Γ ⊢ .all vs (D.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) P : .bool
  | lambda {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} {β : BType} {D : List Term} {e : Term} :
      (vs_nemp : vs ≠ [])
    → (vs_nodup : vs.Nodup)
    → (vs_Γ_disj : ∀ v ∈ vs, v ∉ Γ)
    → (vs_αs_len : vs.length = αs.length)
    → (vs_D_len : vs.length = D.length)
    -- → (typD : ∀ i, Γ ⊢ D.get! i : αs.get! i)
    → (typD : List.Forall₂' D αs (λ Dᵢ αᵢ => Γ ⊢ Dᵢ : .set αᵢ) (vs_D_len ▸ vs_αs_len))
    → (typP : (vs.zipToAList αs ∪ Γ) ⊢ e : β) -- left-biased union
    --------------------------------------------------
    → Γ ⊢ .lambda vs (D.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) e : .set (αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ←List.length_pos_iff] using vs_nemp) ×ᴮ β)
  | app {Γ α β f x}:
      Γ ⊢ f : .set (α ×ᴮ β)
    → Γ ⊢ x : α
    ------------------------
    → Γ ⊢ .app f x : β
  | card {Γ α S}:
      Γ ⊢ S : .set α
    ------------------------
    → Γ ⊢ |S|ᴮ : .int
  | min {Γ S}:
      Γ ⊢ S : .set .int
    ------------------------
    → Γ ⊢ .min S : .int
  | max {Γ S}:
      Γ ⊢ S : .set .int
    ------------------------
    → Γ ⊢ .max S : .int
end

notation:90 Γ:90 " ⊢ " x " : " τ:90 => Typing Γ x τ
notation:90 "⊢ " x " : "  τ:90 => Typing ∅ x τ

end B
