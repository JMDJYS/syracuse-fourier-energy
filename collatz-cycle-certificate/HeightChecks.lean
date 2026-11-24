import FastHeight

/-! Kernel evaluations of the two-rise checker on the initial scales. -/

namespace Cycle108

open Collatz.TwoRise

set_option maxRecDepth 12000
set_option maxHeartbeats 0

def width (k : Nat) : Nat := 2 * k + 101
theorem pairs88 : AllPairs 88 112 := by
  exact allPairs_of_range (rangeCheck_sound
    (show rangeCheck 88 112 32 (width 88) 1 1 88 = true by decide +kernel))

theorem pairs154 : AllPairs 154 178 := by
  exact allPairs_of_range (rangeCheck_sound
    (show rangeCheck 154 178 32 (width 154) 1 1 154 = true by decide +kernel))

theorem pairs259 : AllPairs 259 283 := by
  exact allPairs_of_range (rangeCheck_sound
    (show rangeCheck 259 283 32 (width 259) 1 1 259 = true by decide +kernel))

theorem pairs425 : AllPairs 425 449 := by
  exact allPairs_of_range (rangeCheck_sound
    (show rangeCheck 425 449 32 (width 425) 1 1 425 = true by decide +kernel))

#print axioms pairs425

end Cycle108
