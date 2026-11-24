/- Justin Alick, collatz-m-cycles-101-lean, d1895945, Apache-2.0.
   The local-minimum count extracted from Statements.lean. -/
import Collatz.Defs
import Mathlib.Data.Finset.Card

namespace Collatz

open Finset

/-- The number of local minima in a period of the shortcut map. -/
def numLocalMin (x p : ℕ) : ℕ :=
  ((range p).filter (fun i => T^[i] x % 2 = 1 ∧ T^[i + p - 1] x % 2 = 0)).card

end Collatz
