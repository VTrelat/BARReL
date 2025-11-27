import Lean
import Mathlib.Data.Set.Defs

open Lean Elab Meta

def test : MetaM Expr := do
  let mvar₂ ← mkFreshExprMVar (mkSort 1)
  withLocalDeclD `y mvar₂ λ y ↦ do
    let mem ← mkAppOptM ``Membership.mem #[Int.mkType, .some <| mkApp (.const ``Set []) Int.mkType,none,mkApp (mkConst ``Set.univ [1]) Int.mkType, y]
    mkForallFVars #[y] mem

set_option trace.Meta.isDefEq true in
run_elab do
  let e ← test
  logInfo m!"{indentExpr e}"
  Meta.check e
