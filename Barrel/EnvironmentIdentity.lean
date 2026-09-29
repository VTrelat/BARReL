module
public import Lean.Environment
import all Lean.Environment

open Lean

namespace Barrel

-- Compare every environment field, ignoring only BARReL's own command bookkeeping.
-- Constructor patterns deliberately make Lean layout changes a compilation error.
-- Pointer inequality is a conservative cache miss, even for structurally equal values.
private unsafe def sameExtensionsExcept (skip : Nat)
    (a b : Array EnvExtensionState) : Bool := Id.run do
  if ptrEq a b then return true
  if a.size != b.size then return false
  for i in [:a.size] do
    if i != skip && !ptrEq a[i]! b[i]! then return false
  return true

private unsafe def sameKernelExcept (skip : Nat)
    (a b : Kernel.Environment) : Bool :=
  match a, b with
  | ⟨ac, aq, ad, am, ae, ai, ah⟩, ⟨bc, bq, bd, bm, be, bi, bh⟩ =>
    ptrEq ac bc && aq == bq && ptrEq ad bd && ptrEq am bm &&
      sameExtensionsExcept skip ae be && ptrEq ai bi && ptrEq ah bh

private unsafe def sameEnvironmentExceptImpl (skip : Nat) (a b : Environment) : BaseIO Bool :=
  pure <| match a, b with
  | ⟨⟨ab, ap⟩, ase, ach, ac, aa, ai, al, ar, ax⟩,
    ⟨⟨bb, bp⟩, bse, bch, bc, ba, bi, bl, br, bx⟩ =>
    sameKernelExcept skip ab bb && ptrEq ap bp && ptrEq ase bse &&
      ptrEq ach bch && ptrEq ac bc && ptrEq aa ba && ptrEq ai bi &&
      ptrEq al bl && ptrEq ar br && ax == bx

/--
Check that two snapshots differ only in the specified main-branch extension. All declarations,
other extension states (including attributes), and visibility/realization state must retain
identity. This is an IO observation, not a logical equality test on environments.
-/
@[implemented_by sameEnvironmentExceptImpl]
public opaque sameEnvironmentExcept (skip : Nat) (a b : Environment) : BaseIO Bool := pure false

end Barrel
