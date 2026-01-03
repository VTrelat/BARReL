import Barrel
import Mathlib.Util.AssertNoSorry

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

import machine DerivFalse from "specs"

/-
This machine contains a proof obligation that is not provable:
`∃ x, x ∈ ℤ ∧ x ∉ ℤ`
In Atelier B's interactive prover though, one can still discharge it by
instantiating `x` with `min(∅)` while never verifying well-definedness for
this term. This is reproducible with the following proof script:
```
⊢ ∃ x, x ∈ ℤ ∧ x ∉ ℤ
--------------------
se(min(∅))
--------------------
⊢ min(∅) ∈ ℤ ∧ min(∅) ∉ ℤ
--------------------
mp
--------------------
□
```
-/
prove_obligations_of DerivFalse
next
  exists B.Builtins.min ∅ ?_
  · -- unprovable
    admit
  · refine ⟨?_, ?_⟩
    · exact trivial
    · intro
      generalize_proofs wd at *
      obtain ⟨_, contr, _⟩ := wd
      contradiction

assert_no_sorry DerivFalse.AssertionLemmas_0 -- error
