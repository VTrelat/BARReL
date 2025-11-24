import B.Typing
import Extra.Utils

open Batteries

namespace B

structure SimpleGoal where
  hyps : List Term
  goal : Term

instance : ToString SimpleGoal where
  toString sg := s!"simple goal: {sg.hyps} ⊢ {sg.goal}"

structure ProofObligation where
  name : String
  defs : List Term
  hyps : List Term
  goals : List SimpleGoal

instance : ToString ProofObligation where
  toString po := s!"PO {po.name}:\ndefs:\n{po.defs.printLines}\nhyps:\n{po.hyps.printLines}\n⊢\n{po.goals.printLines}"

instance : EmptyCollection ProofObligation where
  emptyCollection := { name := "", defs := [], hyps := [], goals := [] }

abbrev TermContext := AList (λ _ : 𝒱 => Term)

structure Env where
  context : TypeContext := ∅
  flags : List 𝒱 := []
  freshvarsc : Nat := 0
  defs : TermContext := ∅
  po : List ProofObligation := []
  hypotheses : AssocList DefinitionType <| List Term := AssocList.nil
    |>.cons .ctx []
    |>.cons .seext []
    |>.cons .inv []
    |>.cons .ass []
    |>.cons .lprp []
    |>.cons .inprp []
    |>.cons .inext []
    |>.cons .cst []
    |>.cons .sets []
    |>.cons .mchcst []
    |>.cons .aprp []
    |>.cons .abs []
    |>.cons .imlprp []
    |>.cons .imprp []
    |>.cons .imext []
  distinct : List (List Term) := []
  finite : List Term := []

instance : Inhabited Env := ⟨{}⟩
instance : EmptyCollection Env where
  emptyCollection :=
    { context := (∅ : TypeContext), defs := (∅ : TermContext) }

def EnvToStringAux : AssocList DefinitionType (List Term) → String
  | .nil => ""
  | .cons k v hs => (if v.isEmpty then "" else s!"{nltab}{k}:{nl}{v.printLines}") ++ EnvToStringAux hs
  where nl := "\n"; nltab := nl++"  "

instance : ToString Env where
  toString E :=
    let nl := "\n"
    let nltab := nl++"  "
    s!"Env:{nltab}proof obligations:{nl}{E.po.printLines}{nl}"
      ++ EnvToStringAux E.hypotheses
      ++ s!"{nltab}distinct:{nl}{List.printLines E.distinct}"
      ++ s!"{nl++nltab}context: {E.context}{nltab}flags: {E.flags}{nltab}freshvarsc: {E.freshvarsc}"

end B
