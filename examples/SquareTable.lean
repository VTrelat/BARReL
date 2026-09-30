import Barrel
import Mathlib.Tactic.Ring

/-!
Successive odd increments compute squares. Prove the assertion by induction on the index.
The bundled POG includes Atelier B's source well-definedness obligations.
-/

open B.Builtins

set_option maxHeartbeats 20000 in
import pog SquareTable from "specs/"

obligation AssertionLemmas_0 of SquareTable by
  intro sq nn kk hsq hzero hstep hn
  have squares (n : ℕ) :
      app sq (n : ℤ) (app.WD_of_mem_tfun hsq (Int.natCast_nonneg n)) = (n : ℤ) * n := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      simp only [Nat.cast_succ]
      rw [hstep n (Int.natCast_nonneg n), ih]
      ring
  simpa only [Int.toNat_of_nonneg hn] using squares nn.toNat

obligation WellDefinednessProperties_1 of SquareTable by
  intro sq hsq
  rw [tfun_dom_eq hsq]
  exact show (0 : ℤ) ≤ 0 by omega

obligation WellDefinednessProperties_3 of SquareTable by
  intro sq nn kk hsq _ hk
  rw [tfun_dom_eq hsq]
  change 0 ≤ kk + 1
  have : 0 ≤ kk := hk
  omega

qed SquareTable
