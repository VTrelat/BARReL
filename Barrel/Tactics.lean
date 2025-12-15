import Mathlib.Tactic.Core

namespace Barrel.Tactics
  syntax (name := b_wf) "b_wf" : tactic

  syntax (name := b_typing) "b_typing" : tactic




  syntax (name := auto_solve) "barrel_solve" : tactic

  macro_rules | `(tactic| barrel_solve) => `(tactic| fail "`barrel_solve` failed to solve goal")
  -- macro_rules | `(tactic| barrel_solve) => `(tactic| grind)
  macro_rules | `(tactic| barrel_solve) => `(tactic| b_wf)
  macro_rules | `(tactic| barrel_solve) => `(tactic| b_typing)
  macro_rules | `(tactic| barrel_solve) => `(tactic| trivial)
  macro_rules | `(tactic| barrel_solve) => `(tactic| (repeat1 intro); barrel_solve)
end Barrel.Tactics
