import TailCompute

namespace Cycle108
open Collatz.TwoRise

theorem pairs113037_computed : AllPairs 113037 113061 :=
  allPairs_of_shortCheckAll
    (show shortCheckAll 113037 113061 = true by native_decide)

#print axioms pairs113037_computed
end Cycle108