import RunBudget
import Arithmetic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Geometric and two-rise budgets, evaluated with rational weights. -/

namespace Cycle108

open Finset
open scoped BigOperators

def rationalSum (w : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => rationalSum w n + w n

theorem prefix_cast (w : ℕ → ℚ) (n : ℕ) :
    (rationalSum w n : ℝ) = budget (fun i => (w i : ℝ)) n := by
  induction n with
  | zero => simp [rationalSum, budget]
  | succ n ih => simp only [rationalSum, Rat.cast_add, ih, budget, sum_range_succ]

def geometricWeight (k : ℚ) (i : ℕ) : ℚ := k * growth ^ i

theorem growth_large : (1 : ℚ) < growth := by norm_num [growth]

theorem geometricWeight_mono {k : ℚ} (hk : 0 ≤ k) : Monotone (geometricWeight k) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ growth_large.le hab) hk

theorem geometric_prefix (k : ℚ) (n : ℕ) : rationalSum (geometricWeight k) n = k * geo n := by
  have hd : growth - 1 ≠ 0 := sub_ne_zero.mpr growth_large.ne'
  induction n with
  | zero => simp [rationalSum, geo]
  | succ n ih =>
    simp only [rationalSum, ih, geometricWeight, geo, pow_succ]
    field_simp [hd]
    ring

def gridWeight (i : ℕ) : ℚ :=
  if i < 34 then
    (if i % 2 = 0 then 1 else growth) * (leanCaps.getD (i / 2) 0 : ℚ)
  else geometricWeight 283999 (i - 34)

theorem gridWeight_at_zero : gridWeight 0 = 88 := by decide +kernel

theorem gridWeight_small : ∀ i : Fin 34,
    gridWeight i.val ≤ gridWeight (i.val+1) := by decide +kernel

theorem gridWeight_mono : Monotone gridWeight := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 34
  · exact gridWeight_small ⟨n,hn⟩
  · have h := geometricWeight_mono (k := 283999) (by norm_num)
        (show n - 34 ≤ n+1 - 34 by omega)
    simpa only [gridWeight, if_neg hn,
      if_neg (show ¬ n+1 < 34 by omega)] using h

theorem gridWeight_nonneg (i : ℕ) : 0 ≤ gridWeight i := by
  have h := gridWeight_mono (Nat.zero_le i)
  rw [gridWeight_at_zero] at h
  linarith

theorem grid_prefix99 : rationalSum gridWeight 99 = gridBudget 99 := by decide +kernel
theorem grid_prefix107 : rationalSum gridWeight 107 = gridBudget 107 := by decide +kernel

theorem budget_le_mono {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) :
    Monotone (budget w) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [budget, sum_range_succ]
  exact le_add_of_nonneg_right (hw n)

theorem budget_extra {w : ℕ → ℝ} (hw : Monotone w) (a b : ℕ) :
    budget w a + (b : ℝ)*w 0 ≤ budget w (a+b) := by
  simp only [budget, sum_range_add]
  apply add_le_add_left
  have h := sum_le_sum (fun i (_ : i ∈ range b) => hw (Nat.zero_le (a+i)))
  simpa only [sum_const, card_range, nsmul_eq_mul] using h

theorem priced_from_low {a w : ℕ → ℝ} {low : ℕ → Bool}
    (hw : Monotone w) (hwn : ∀ n, 0 ≤ w n)
    (h0 : low 0 = true) (hbound : ∀ i, low i = true → ∀ d, a (i+d) ≤ w d)
    {n b : ℕ} (hn : n ≤ 107) (hb : 1 ≤ b) (hL : b ≤ n - highCount low n) :
    budget a n ≤ ((b-1 : ℕ) : ℝ)*w 0 + budget w (108-b) := by
  let L := n-highCount low n
  let C := highCount low n
  have hCL : C + L = n := by
    have h := highCount_le low n
    dsimp [L,C]
    omega
  have h := reset_budget h0 hw hbound n
  change _ ≤ L • w 0 + budget (fun i => w (i+1)) C at h
  have hsplit : budget w (C+1) = w 0 + budget (fun i => w (i+1)) C := by
    simp [budget, sum_range_succ', add_comm]
  have hLa : L = (b-1) + (L-b) + 1 := by omega
  have hnum : C+1+(L-b) ≤ 108-b := by omega
  have hcu := (budget_extra hw (C+1) (L-b)).trans ((budget_le_mono hwn) hnum)
  rw [nsmul_eq_mul] at h
  have he : (L : ℝ) = ((b-1 : ℕ) : ℝ) + ((L-b : ℕ) : ℝ) + 1 := by exact_mod_cast hLa
  linarith only [h, hsplit, congrArg (fun x : ℝ => x * w 0) he, hcu]

#print axioms grid_prefix107
#print axioms priced_from_low

end Cycle108
