import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The unimodular and low-return arguments in Section 4. -/

namespace Cycle108

open Finset
open scoped BigOperators

theorem unimodular_bound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p q r w t s : ℤ} {u v : K}
    (hdet : p * w - q * r = 1) (hq : 0 < q) (hw : 0 < w)
    (hs : 0 < s) (hstop : s < q + w)
    (hu : 0 < (p : K) * u - (q : K) * v)
    (hv : (r : K) * u - (w : K) * v < 0)
    (hts : 0 < (t : K) * u - (s : K) * v) :
    (p : K) * u - (q : K) * v ≤ (t : K) * u - (s : K) * v := by
  let a := t * w - r * s
  let b := p * s - q * t
  have ht : t = a * p + b * r := by dsimp [a, b]; linear_combination -t * hdet
  have he : s = a * q + b * w := by dsimp [a, b]; linear_combination -s * hdet
  have hgap : (t : K) * u - (s : K) * v =
      (a : K) * ((p : K) * u - (q : K) * v) +
      (b : K) * ((r : K) * u - (w : K) * v) := by
    have ht' : (t : K) = (a : K) * p + (b : K) * r := by exact_mod_cast ht
    have he' : (s : K) = (a : K) * q + (b : K) * w := by exact_mod_cast he
    rw [ht', he']
    ring
  have ha : 1 ≤ a := by
    by_contra h
    have ha' : a ≤ 0 := by omega
    have hb : b < 0 := by
      by_contra hb
      have h1 := mul_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast ha' : (a : K) ≤ 0) hu.le
      have h2 := mul_nonpos_of_nonneg_of_nonpos
        (by exact_mod_cast (le_of_not_gt hb) : (0 : K) ≤ (b : K)) hv.le
      linarith
    linarith only [he, hs, mul_nonpos_of_nonpos_of_nonneg ha' hq.le,
      mul_neg_of_neg_of_pos hb hw]
  have hb : b ≤ 0 := by
    by_contra h
    have h1 := mul_le_mul_of_nonneg_right ha hq.le
    have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ b by omega) hw.le
    linarith
  have h1 := mul_le_mul_of_nonneg_right
    (by exact_mod_cast ha : (1 : K) ≤ (a : K)) hu.le
  have h2 := mul_nonneg_of_nonpos_of_nonpos
    (by exact_mod_cast hb : (b : K) ≤ 0) hv.le
  linarith

def budget {K : Type*} [AddCommMonoid K] (w : ℕ → K) (n : ℕ) : K :=
  ∑ i ∈ range n, w i

theorem budget_superadditive {K : Type*} [AddCommMonoid K] [PartialOrder K] [IsOrderedAddMonoid K]
    {w : ℕ → K} (hw : Monotone w) (a b : ℕ) :
    budget w a + budget w b ≤ budget w (a + b) := by
  simp only [budget, sum_range_add]
  apply add_le_add_left
  exact sum_le_sum (fun i _ => hw (by omega))

/-- The list records one less than the number of runs in each arc. -/
theorem low_return_budget {K : Type*} [AddCommMonoid K] [PartialOrder K] [IsOrderedAddMonoid K]
    {w : ℕ → K} (hw : Monotone w) (arcs : List ℕ) :
    (arcs.map (fun j => budget w (j + 1))).sum ≤
      arcs.length • w 0 + budget (fun j => w (j + 1)) arcs.sum := by
  induction arcs with
  | nil => simp [budget]
  | cons j js ih =>
    have hj : budget w (j + 1) = w 0 + budget (fun i => w (i + 1)) j := by
      simp [budget, sum_range_succ', add_comm]
    have hs := budget_superadditive (fun a b hab => hw (Nat.add_le_add_right hab 1)) j js.sum
    simp only [List.map_cons, List.sum_cons, List.length_cons, succ_nsmul, hj]
    exact (add_le_add_left ih _).trans (by
      simpa only [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hs (js.length • w 0 + w 0))

#print axioms unimodular_bound
#print axioms low_return_budget

end Cycle108
