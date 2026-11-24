import ReducedHeight

/-! Reflecting the complete range check, with a separate modulus for each
interval of first-rise lengths. -/

namespace Cycle108

open Collatz.TwoRise

def chunkStart (i : Nat) : Nat := i * 700 + 1
def chunkSize (N i : Nat) : Nat := min 700 (N - i * 700)
def chunkWidth (N i : Nat) : Nat := 2 * (N - i * 700) + 101

def checkChunk (N B i : Nat) : Bool :=
  let w := chunkWidth N i
  reducedRange N B 24 w (chunkStart i)
    (powMod (2^w) 21 ((2^w+1)/3) (i*700) 1) (chunkSize N i)

def checkAllPairs (N B : Nat) : Bool :=
  (List.range ((N+699)/700)).all (checkChunk N B)

theorem allPairs_of_checkAllPairs {N B : Nat} (h : checkAllPairs N B = true) :
    AllPairs N B := by
  intro a ha hNa
  let i := (a-1)/700
  have hi : i < (N+699)/700 := by dsimp [i]; omega
  have hac : chunkStart i ≤ a := by dsimp [chunkStart, i]; omega
  have han : a < chunkStart i + chunkSize N i := by
    have hq : a-1 < (i+1)*700 := by dsimp [i]; omega
    unfold chunkStart chunkSize
    omega
  have hb : checkChunk N B i = true := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  change reducedRange N B 24 (chunkWidth N i) (chunkStart i) _ (chunkSize N i) = true at hb
  exact reducedRange_sound hb a hac han hNa

#print axioms allPairs_of_checkAllPairs

end Cycle108
