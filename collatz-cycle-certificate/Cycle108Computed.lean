import FromCycle
import HeightChecks
import GridMiddle
import GridLarge1
import GridLarge2
import GridComputed3
import GridComputed4
import GridComputed5
import Mathlib.Tactic.FinCases

namespace Cycle108

open Collatz

theorem verified_grid_computed : VerifiedGrid := by
  intro j
  fin_cases j
  · exact pairs88
  · exact pairs154
  · exact pairs259
  · exact pairs425
  · exact pairs688
  · exact pairs1105
  · exact pairs1766
  · exact pairs2814
  · exact pairs4475
  · exact pairs7107
  · exact pairs11279
  · exact pairs17891
  · exact pairs28371
  · exact pairs44982
  · exact pairs71309_computed
  · exact pairs113037_computed
  · exact pairs179174_computed

/-- Theorem 4.1, with the two cited mathematical inputs as parameters. -/
theorem no_107_cycle_computed (hX : ∀ n, 0 < n → n < 2^71 → Reaches T n 1) (hR : RhinBound)
    {x t : ℕ} (hx : 0 < x) (ht : 0 < t) (hcycle : T^[t] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) : 108 ≤ numLocalMin x t :=
  no_107_cycle_of_grid (verifiedThroughFloor_of_below hX) hR verified_grid_computed hx ht hcycle hx1 hx2

#check no_107_cycle_computed
#print axioms no_107_cycle_computed

end Cycle108
