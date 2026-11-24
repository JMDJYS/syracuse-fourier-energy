import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum

/-! The exact numerical inequalities of the cycle certificate in Section 4. -/

namespace Cycle108

def floorHeight : ℕ := 2 ^ 71
def growth : ℚ := 1584962501 / 1000000000
def rhinExponent : ℚ := 133 / 10
def rhinShift : ℚ := 46057 / 100000
def tailStart : ℕ := 5225419486637257521420827

structure Bracket where
  p : ℕ
  q : ℕ
  r : ℕ
  w : ℕ
  gap : ℚ

def bracket1 : Bracket := ⟨630118245525664765, 397560349370386783,
  6724555128221608268, 4242721909926539673, 358⟩
def bracket2 : Bracket := ⟨7354673373747273033, 4640282259296926456,
  36143248623210700400, 22803850947114245497, 63⟩
def bracket3 : Bracket := ⟨43497921996957973433, 27444133206411171953,
  79641170620168673833, 50247984153525417450, 239 / 10⟩
def bracket4 : Bracket := ⟨123139092617126647266, 77692117359936589403,
  202780263237295321099, 127940101513462006853, 803 / 100⟩
def bracket5 : Bracket := ⟨49373105075258054570781, 31150961018190238869556,
  2727782575569043909543559, 1721039188200292347893905, 9 / 10000⟩
def bracket6 : Bracket := ⟨2777155680644301964114340, 1752190149218482586763461,
  5504938256213345873657899, 3473229337418774934657366, 46 / 100000⟩

def Bracket.stop (b : Bracket) : ℕ := b.q + b.w

def logPartial (z : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => logPartial z n + 2 * z ^ (2 * n + 1) / (2 * (n : ℚ) + 1)

def logTail (z : ℚ) (n : ℕ) : ℚ :=
  2 * z ^ (2 * n + 1) / ((2 * (n : ℚ) + 1) * (1 - z ^ 2))

def log2Lo : ℚ := logPartial (1 / 3) 120
def log2Hi : ℚ := log2Lo + logTail (1 / 3) 120
def log3Lo : ℚ := logPartial (1 / 2) 120
def log3Hi : ℚ := log3Lo + logTail (1 / 2) 120

def Bracket.valid (b : Bracket) : Prop :=
  b.p * b.w = b.q * b.r + 1 ∧
  b.gap < floorHeight * (b.p * log2Lo - b.q * log3Hi) ∧
  (b.r : ℚ) * log2Hi < b.w * log3Lo ∧ 0 < b.gap

theorem bracket1_valid : bracket1.valid := by
  unfold Bracket.valid
  decide +kernel
theorem bracket2_valid : bracket2.valid := by
  unfold Bracket.valid
  decide +kernel
theorem bracket3_valid : bracket3.valid := by
  unfold Bracket.valid
  decide +kernel
theorem bracket4_valid : bracket4.valid := by
  unfold Bracket.valid
  decide +kernel
theorem bracket5_valid : bracket5.valid := by
  unfold Bracket.valid
  decide +kernel
theorem bracket6_valid : bracket6.valid := by
  unfold Bracket.valid
  decide +kernel

theorem stop6 : bracket6.stop = tailStart := by decide +kernel
theorem growth_check : log3Hi < growth * log2Lo := by decide +kernel
theorem rhin_check : rhinExponent * rhinShift < 9 * log2Lo := by decide +kernel

def geo (j : ℕ) : ℚ := (growth ^ j - 1) / (growth - 1)

def caps : List ℕ :=
  [88, 145, 235, 378, 605, 964, 1533, 2435, 3865, 6131, 9723,
   15416, 24444, 38753, 61428, 97372, 154343, 301000]

def pairedBudget (j : ℕ) : ℚ :=
  let entries := caps.dropLast.flatMap (fun k => [(k : ℚ), growth * (k : ℚ)])
  (entries.take j).sum + 301000 * geo (j - entries.length)

theorem tail_check : geo 107 * (7 + 10 + rhinExponent * 83) < tailStart := by
  decide +kernel

theorem low2_check : 56 + (51 : ℚ) / 2 ^ 3 ≤ bracket2.gap := by decide +kernel
theorem low3_check : 23 + (84 : ℚ) / 2 ^ 7 ≤ bracket3.gap := by decide +kernel
theorem low4_check : 8 + (99 : ℚ) / 2 ^ 12 ≤ bracket4.gap := by decide +kernel

theorem band2_check : 74 * (geo 51 + 56) < bracket1.stop := by decide +kernel
theorem band3_check : 78 * (geo 84 + 23) < bracket2.stop := by decide +kernel
theorem band4_check : pairedBudget 99 + 8 * 88 < bracket3.stop := by decide +kernel
theorem band5_check : pairedBudget 107 < bracket4.stop := by decide +kernel
theorem band6_check : 89 * geo 107 < bracket5.stop := by decide +kernel

theorem min5_check : (107 : ℚ) < bracket5.gap * 2 ^ 17 := by decide +kernel
theorem min6_check : (107 : ℚ) < bracket6.gap * 2 ^ 18 := by decide +kernel

/-- A slightly looser grid adapted to the verified two-rise odd-count checker.
Its last cap is smaller than the final cap used in the Python certificate. -/
def leanCaps : List ℕ :=
  [88, 154, 259, 425, 688, 1105, 1766, 2814, 4475, 7107, 11279,
   17891, 28371, 44982, 71309, 113037, 179174, 283999]

def gridBudget (j : ℕ) : ℚ :=
  let entries := leanCaps.dropLast.flatMap (fun k => [(k : ℚ), growth * (k : ℚ)])
  (entries.take j).sum + 283999 * geo (j - entries.length)

theorem grid99_le : gridBudget 99 ≤ pairedBudget 99 := by decide +kernel
theorem grid107_le : gridBudget 107 ≤ pairedBudget 107 := by decide +kernel

theorem grid_caps_check : ∀ j : Fin 17,
    (leanCaps.getD j.val 0 : ℚ) +
        (growth - 1) * (leanCaps.getD j.val 0 + 24) ≤ leanCaps.getD (j.val+1) 0 := by
  decide +kernel

#print axioms bracket6_valid
#print axioms band5_check

end Cycle108
