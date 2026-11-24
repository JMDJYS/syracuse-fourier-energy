import Dynamics
import Profile

/-! Reduction of an actual nontrivial positive Collatz cycle to its local
minima and application of the certified interval exclusion. -/

namespace Cycle108

open Collatz Finset
open scoped BigOperators

def VerifiedThroughFloor : Prop :=
  ∀ n, 0 < n → n ≤ 2^71 → Reaches T n 1

theorem two_pow_reaches_one (k : ℕ) : Reaches T (2^k) 1 := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨steps, hsteps⟩ := ih
    refine ⟨steps+1, ?_⟩
    have hstep : T (2^(k+1)) = 2^k := by
      rw [Nat.pow_succ, T_even (by omega)]
      omega
    rw [Function.iterate_succ_apply, hstep]
    exact hsteps

theorem verifiedThroughFloor_of_below
    (h : ∀ n, 0 < n → n < 2^71 → Reaches T n 1) : VerifiedThroughFloor := by
  intro n hn hle
  by_cases hlt : n < 2^71
  · exact h n hn hlt
  · rw [show n = 2^71 by omega]
    exact two_pow_reaches_one 71

def RhinBound : Prop :=
  ∀ x p : ℕ, 0 < x → 0 < p → T^[p] x = x → x ≠ 1 → x ≠ 2 →
    1 ≤ oddCount T x p →
    Real.exp (-(rhinExponent : ℝ) *
      ((rhinShift : ℝ) + Real.log (oddCount T x p))) <
      lnGap p (oddCount T x p)

def VerifiedGrid : Prop :=
  ∀ j : Fin 17, TwoRise.AllPairs (leanCaps.getD j.val 0) (leanCaps.getD j.val 0 + 24)

theorem no_107_cycle_of_grid (hX : VerifiedThroughFloor) (hR : RhinBound)
    (hGrid : VerifiedGrid)
    {x t : ℕ} (hx : 0 < x) (ht : 0 < t) (hcycle : T^[t] x = x)
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) : 108 ≤ numLocalMin x t := by
  obtain ⟨i, hmin, hleast⟩ := exists_least_rotation hx ht hcycle
  let y := T^[i] x
  let M := numLocalMin y t
  let s := oddCount T y t
  let n := fun j => nextMin^[j] y
  let a := fun j => orun (n j)
  have hy : 0 < y := iterate_T_pos hx i
  have hcy : T^[t] y = y := cycle_rotate hcycle i
  have hfloor := cycle_gt_of_verified hX hx ht hcycle hx1 hx2
  have hyA : 2^71 < y := hfloor i
  have hnstep : ∀ j, n (j+1) = nextMin (n j) := by
    intro j
    exact Function.iterate_succ_apply' nextMin j y
  have hnp : ∀ j, 0 < n j := nextMin_iterate_pos hy
  have hno : ∀ j, n j % 2 = 1 := nextMin_iterate_odd hy hmin.1
  have hnT : ∀ j, n j = T^[i + minPos y j] x := by
    intro j
    change nextMin^[j] y = _
    rw [← iterate_minPos j]
    change (T^[minPos y j]) (T^[i] x) = _
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have hM : 0 < M := by
    unfold M numLocalMin
    apply card_pos.mpr
    refine ⟨0, mem_filter.2 ⟨mem_range.mpr ht, ?_⟩⟩
    simpa [IsMinOf] using hmin
  have hs := oddCount_eq_sum_orun hy ht hcy hmin
  change s = ∑ j ∈ range M, a j at hs
  have hspos : 0 < s := by
    rw [hs]
    have hn0 : 0 < a 0 := orun_pos (hno 0)
    exact hn0.trans_le (single_le_sum (fun j (_ : j ∈ range M) => Nat.zero_le (a j))
      (mem_range.2 hM))
  let profile : CycleProfile M t s :=
    { minimum := n
      length := a
      least := by
        intro j
        rw [hnT j]
        exact hleast _
      floor := by
        intro j
        rw [hnT j]
        exact hfloor _
      minimaPositive := hM
      oddPositive := hspos
      lengthTotal := by
        unfold budget
        rw [hs, Nat.cast_sum]
      rise := by
        intro j
        exact orun_le_logb (n j)
      single := by
        intro j
        rw [hnstep]
        have h := logb_nextMin_lt (hnp j) (hno j)
        have hpos : 0 ≤ heightLog (n j) :=
          Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (n j)])
        exact h.le.trans (mul_le_mul_of_nonneg_right logb_three_lt_growth.le hpos)
      double := by
        intro j k hk
        rw [show j+2 = (j+1)+1 from rfl, hnstep (j+1), hnstep j]
        have h := logb_two_step (hno j)
        have hsN := twoRiseBound_of_allPairs (hGrid k) (n j) (hno j) (lt_of_heightLog_le hk)
        have hsR : ((orun (n j) + orun (nextMin (n j)) : ℕ) : ℝ) ≤
            ((leanCaps.getD k.val 0 + 24 : ℕ) : ℝ) := by exact_mod_cast hsN
        have hd : (0 : ℝ) ≤ growthR - 1 := by norm_num [growthR, growth]
        have hmul := mul_le_mul (sub_le_sub_right logb_three_lt_growth.le 1) hsR
          (by positivity) hd
        have hn3 : (3 : ℝ) ≤ (n j : ℝ)+1 := by
          have hn' : 2 ≤ n j := by
            rw [hnT j]
            exact (by norm_num : 2 ≤ 2^71).trans (hfloor _).le
          exact_mod_cast (show 3 ≤ n j + 1 by omega)
        have hd6 : 6 / ((n j : ℝ)+1) ≤ 2 := by
          apply (div_le_iff₀ (by positivity)).2
          linarith
        have hnumeric := grid_caps_check k
        have hcast : ((leanCaps.getD k.val 0 : ℕ) : ℝ) +
            (growthR - 1) * ((leanCaps.getD k.val 0 + 24 : ℕ) : ℝ) ≤
            (leanCaps.getD (k.val+1) 0 : ℝ) := by
          unfold growthR
          exact_mod_cast hnumeric
        unfold heightLog at hk ⊢
        unfold growthR at hcast
        linarith only [hk, h, hmul, hd6, hcast]
      reciprocals := by
        have h16 := theorem16_of_isMin hy ht hcy hmin
        change 3 * lnGap t s ≤ ∑ j ∈ range M, riseSum (n j) (orun (n j)) at h16
        have hj : ∀ j, riseSum (n j) (orun (n j)) < 3 / (n j : ℝ) := by
          intro j
          have hl := riseSum_lt (hnp j) (fun _ h => odd_of_lt_orun h)
          linarith
        have hS := sum_lt_sum (fun j (_ : j ∈ range M) => (hj j).le)
          ⟨0, mem_range.2 hM, hj 0⟩
        have e : (∑ j ∈ range M, (3 : ℝ) / (n j : ℝ)) =
            3 * budget (fun j => 1 / (n j : ℝ)) M := by
          simp only [budget, Finset.mul_sum, mul_one_div]
        rw [e] at hS
        linarith only [h16,hS]
      rhin := by
        exact hR y t hy ht hcy (by omega) (by omega) hspos }
  have hl := lower_bound_of_profile profile
  simpa only [M, y, numLocalMin_rotate ht hcycle i] using hl

#print axioms no_107_cycle_of_grid

end Cycle108
