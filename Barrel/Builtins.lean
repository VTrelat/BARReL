import Barrel.Builtins.Relation
import Barrel.Builtins.Function
import Barrel.Builtins.Power
import Barrel.Builtins.Arithmetic

section Lemmas
open B.Builtins

@[grind =, simp]
theorem SetRel.image_insert {α β : Type _} (f : SetRel α β) (a : α) (S : Set α) :
    f[insert a S] = f[{a}] ∪ f[S] := by ext; simp

end Lemmas


/-
TODO: add remaining Unicode characters

`/<<:` ≔ `⊄`
`/<:` ≔ `⊈`
`/:` ≔ `∉`
`<=>` ≔ `⇔`
`/=` ≔ `≠`
`<=` ≔ `≤`
`>=` ≔ `≥`
`<<:` ≔ `⊂`
`<:` ≔ `⊆`
`{}` ≔ `∅`
`\` ≔ `∖`
`**` ≔ `×`
`<+` ≔ `` (missing)
`><` ≔ `⊗`
`||` ≔ `∥`
`~` ≔ `∼`
`:=` ≔ `≔`

-/
