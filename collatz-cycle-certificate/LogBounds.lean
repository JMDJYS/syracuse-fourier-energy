import Arithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! From the exact rational partial sums to bounds on the real logarithms. -/

namespace Cycle108

open Finset
open scoped BigOperators

theorem logPartial_real (z : ℚ) (n : ℕ) :
    (logPartial z n : ℝ) =
      ∑ j ∈ range n, 2 * (z : ℝ) ^ (2*j+1) / (2*(j : ℝ)+1) := by
  induction n with
  | zero => simp [logPartial]
  | succ n ih => rw [logPartial, sum_range_succ]; push_cast; rw [ih]

theorem log_box_sound {z : ℚ} (hz : 0 ≤ (z : ℝ)) (hz' : (z : ℝ) < 1) (n : ℕ) :
    (logPartial z n : ℝ) ≤ Real.log (1+(z : ℝ)) - Real.log (1-(z : ℝ)) ∧
      Real.log (1+(z : ℝ)) - Real.log (1-(z : ℝ)) ≤
        (logPartial z n : ℝ) + (logTail z n : ℝ) := by
  let x := (z : ℝ)
  let f := fun j : ℕ => 2 * x ^ (2*j+1) / (2*(j : ℝ)+1)
  have hx : 0 ≤ x := hz
  have h : HasSum f (Real.log (1+x) - Real.log (1-x)) := by
    convert Real.hasSum_log_sub_log_of_abs_lt_one
      (show |x| < 1 by rw [abs_of_nonneg hx]; exact hz') using 1
    ext j
    dsimp [f]
    ring
  have ht : Summable (fun j => f (j+n)) :=
    (summable_nat_add_iff n).2 h.summable
  have hsum := h.summable.sum_add_tsum_nat_add n
  rw [h.tsum_eq] at hsum
  have hl : (0 : ℝ) ≤ ∑' j, f (j+n) := by
    apply tsum_nonneg
    intro j
    dsimp [f]
    positivity
  let c := 2 * x ^ (2*n+1) / (2*(n : ℝ)+1)
  have hx2 : x ^ 2 < 1 := by nlinarith [mul_le_mul_of_nonneg_left hz'.le hz]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg x) hx2).mul_left c
  have huv : ∀ j : ℕ, f (j+n) ≤ c * (x^2)^j := by
    intro j
    have he : x ^ (2*(j+n)+1) = x ^ (2*n+1) * (x^2)^j := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hd : (2*(n : ℝ)+1) ≤ 2*((j+n : ℕ) : ℝ)+1 := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) j]
    dsimp [f, c]
    rw [he]
    calc
      _ = 2 * x ^ (2*n+1) * (x^2)^j / (2*((j+n : ℕ) : ℝ)+1) := by ring
      _ ≤ 2 * x ^ (2*n+1) * (x^2)^j / (2*(n:ℝ)+1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = _ := by ring
  have hupper := ht.tsum_le_tsum huv hg.summable
  rw [hg.tsum_eq] at hupper
  have heq : c * (1-x^2)⁻¹ = (logTail z n : ℝ) := by
    unfold logTail
    push_cast
    change (2 * x ^ (2*n+1) / (2*(n:ℝ)+1)) * (1-x^2)⁻¹ =
      2 * x ^ (2*n+1) / ((2*(n:ℝ)+1)*(1-x^2))
    rw [← div_div]
    rfl
  rw [heq] at hupper
  rw [logPartial_real]
  change (∑ j ∈ range n, f j) ≤ _ ∧ _ ≤ (∑ j ∈ range n, f j) + _
  exact ⟨by linarith, by linarith⟩

theorem log2_enclosed : (log2Lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (log2Hi : ℝ) := by
  have h := log_box_sound (z := 1/3) (by norm_num) (by norm_num) 120
  have e : Real.log (1 + ((1/3 : ℚ) : ℝ)) - Real.log (1 - ((1/3 : ℚ) : ℝ)) =
      Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [e] at h
  simpa only [log2Lo, log2Hi, Rat.cast_add] using h

theorem log3_enclosed : (log3Lo : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (log3Hi : ℝ) := by
  have h := log_box_sound (z := 1/2) (by norm_num) (by norm_num) 120
  have e : Real.log (1 + ((1/2 : ℚ) : ℝ)) - Real.log (1 - ((1/2 : ℚ) : ℝ)) =
      Real.log 3 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [e] at h
  simpa only [log3Lo, log3Hi, Rat.cast_add] using h

#print axioms log3_enclosed

end Cycle108
