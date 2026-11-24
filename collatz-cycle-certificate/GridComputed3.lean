import TailCompute

namespace Cycle108
open Collatz.TwoRise

theorem pairs71309_computed : AllPairs 71309 71333 :=
  allPairs_of_shortCheckAll
    (show shortCheckAll 71309 71333 = true by native_decide)

#print axioms pairs71309_computed
end Cycle108