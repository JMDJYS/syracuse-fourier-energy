import TailCompute

namespace Cycle108
open Collatz.TwoRise

theorem pairs179174_computed : AllPairs 179174 179198 :=
  allPairs_of_shortCheckAll
    (show shortCheckAll 179174 179198 = true by native_decide)

#print axioms pairs179174_computed
end Cycle108