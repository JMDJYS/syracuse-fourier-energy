import BandLogic
import GrowthProfiles
import Tail

/-! The exclusion of a cycle profile using the verified numeric bounds. -/

namespace Cycle108

open Finset
open scoped BigOperators

noncomputable def heightLog (n : ℕ) : ℝ := Real.logb 2 ((n : ℝ)+1)
noncomputable def lnGap (t s : ℕ) : ℝ := (t : ℝ)*Real.log 2 - (s : ℝ)*Real.log 3

theorem heightLog_le_of_lt {n k : ℕ} (h : n < 2^k) : heightLog n ≤ k := by
  have hn : (n : ℝ)+1 ≤ (2 : ℝ)^k := by exact_mod_cast Nat.succ_le_of_lt h
  have ht := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hn
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at ht

theorem lt_of_heightLog_le {n k : ℕ} (h : heightLog n ≤ k) : n < 2^k := by
  have ht := (Real.logb_le_iff_le_rpow (b := 2) (by norm_num)
    (show 0 < (n : ℝ)+1 by positivity)).1 h
  rw [Real.rpow_natCast] at ht
  exact Nat.lt_of_succ_le (by exact_mod_cast ht)

structure CycleProfile (M t s : ℕ) where
  minimum : ℕ → ℕ
  length : ℕ → ℕ
  least : ∀ j, minimum 0 ≤ minimum j
  floor : ∀ j, floorHeight < minimum j
  minimaPositive : 0 < M
  oddPositive : 0 < s
  lengthTotal : (s : ℝ) = budget (fun j => (length j : ℝ)) M
  rise : ∀ j, (length j : ℝ) ≤ heightLog (minimum j)
  single : ∀ j, heightLog (minimum (j+1)) ≤ growthR * heightLog (minimum j)
  double : ∀ i (j : Fin 17), heightLog (minimum i) ≤ leanCaps.getD j.val 0 →
    heightLog (minimum (i+2)) ≤ leanCaps.getD (j.val+1) 0
  reciprocals : lnGap t s < budget (fun j => 1 / (minimum j : ℝ)) M
  rhin : Real.exp (-(rhinExponent : ℝ) * ((rhinShift : ℝ) + Real.log s)) < lnGap t s

def CycleProfile.low {M t s : ℕ} (p : CycleProfile M t s) (h : ℕ) (j : ℕ) : Bool :=
  decide (p.minimum j < 2 ^ (71+h))

theorem CycleProfile.minimumPositive {M t s : ℕ} (p : CycleProfile M t s) (j : ℕ) :
    0 < p.minimum j := (Nat.zero_le _).trans_lt (p.floor j)

theorem CycleProfile.gap_minimum {M t s : ℕ} (p : CycleProfile M t s) :
    lnGap t s < (M : ℝ) / (p.minimum 0 : ℝ) := by
  apply p.reciprocals.trans_le
  have hi (i : ℕ) : (1 : ℝ) / (p.minimum i : ℝ) ≤ 1 / (p.minimum 0 : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast p.minimumPositive 0)
      (by exact_mod_cast p.least i)
  have h := sum_le_sum (s := range M) (fun i _ => hi i)
  simpa only [budget, sum_const, card_range, nsmul_eq_mul, mul_one_div] using h

theorem CycleProfile.low_at_zero {M t s : ℕ} (p : CycleProfile M t s)
    {h : ℕ} (hl : 0 < M - highCount (p.low h) M) : p.low h 0 = true := by
  by_contra h0
  have hf : (range M).filter (fun j => p.low h j = false) = range M := by
    apply filter_eq_self.2
    intro j _
    suffices 2 ^ (71+h) ≤ p.minimum j by simp [CycleProfile.low, not_lt_of_ge this]
    have h0' : 2 ^ (71+h) ≤ p.minimum 0 := by
      simpa [CycleProfile.low] using h0
    exact h0'.trans (p.least j)
  simp [highCount, hf] at hl

theorem sum_low_price (low : ℕ → Bool) (c : ℝ) (n : ℕ) :
    budget (fun i => if low i then 1 else c) n =
      ((n-highCount low n : ℕ) : ℝ) + (highCount low n : ℝ)*c := by
  induction n with
  | zero => simp [budget, highCount]
  | succ n ih =>
    have e : budget (fun i => if low i then (1:ℝ) else c) (n+1) =
        budget (fun i => if low i then 1 else c) n + (if low n then 1 else c) :=
      sum_range_succ _ _
    rw [e, ih, highCount_succ]
    have hlo := highCount_le low n
    cases h : low n with
    | true =>
      simp only [if_true, Nat.add_zero]
      rw [show n+1-highCount low n = n-highCount low n+1 by omega]
      push_cast
      ring
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [show n+1-(highCount low n+1) = n-highCount low n by omega]
      push_cast
      ring

theorem CycleProfile.scaled_reciprocal {M t s : ℕ} (p : CycleProfile M t s) (h : ℕ) :
    scaledGap (Real.log 2) (Real.log 3) t s <
      ((M-highCount (p.low h) M : ℕ) : ℝ) +
        ((M : ℝ) - ((M-highCount (p.low h) M : ℕ) : ℝ)) / 2^h := by
  have he : (0 : ℝ) < floorHeight := by unfold floorHeight; positivity
  have hC := highCount_le (p.low h) M
  have hc : (highCount (p.low h) M : ℝ) =
      (M : ℝ) - ((M-highCount (p.low h) M : ℕ) : ℝ) := by rw [Nat.cast_sub hC]; ring
  unfold scaledGap
  have hp := mul_lt_mul_of_pos_left p.reciprocals he
  apply hp.trans_le
  unfold budget
  rw [Finset.mul_sum]
  have hpt : ∀ i : ℕ, (floorHeight : ℝ) * (1 / (p.minimum i : ℝ)) ≤
      if p.low h i then 1 else 1 / 2^h := by
    intro i
    have hm : (0 : ℝ) < p.minimum i := by exact_mod_cast p.minimumPositive i
    rw [mul_one_div]
    cases hi : p.low h i with
    | true =>
      simp only [if_true]
      apply (div_le_iff₀ hm).2
      have hh : (floorHeight : ℝ) < (p.minimum i : ℝ) := by exact_mod_cast p.floor i
      linarith
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have hn : 2^(71+h) ≤ p.minimum i := by simpa [CycleProfile.low] using hi
      rw [pow_add, ← show floorHeight = 2^71 from rfl] at hn
      apply (div_le_div_iff₀ hm (by positivity : (0 : ℝ) < 2^h)).2
      have hn' : (floorHeight : ℝ) * 2^h ≤ (p.minimum i : ℝ) := by exact_mod_cast hn
      simpa only [one_mul] using hn'
  have hsum := sum_le_sum (s := range M) (fun i _ => hpt i)
  have hprice := sum_low_price (p.low h) (1 / (2 : ℝ)^h) M
  unfold budget at hprice
  rw [hprice, hc, mul_one_div] at hsum
  exact hsum

theorem CycleProfile.scaled_upper {M t s : ℕ} (p : CycleProfile M t s) :
    scaledGap (Real.log 2) (Real.log 3) t s < (M : ℝ) := by
  have h := p.scaled_reciprocal 0
  simp only [pow_zero, div_one] at h
  linarith

theorem geo_mono : Monotone geo := by
  intro a b hab
  unfold geo
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (pow_le_pow_right₀ growth_large.le hab) _)
    (by linarith [growth_large])

theorem geo_nonneg (n : ℕ) : 0 ≤ geo n := by
  simpa [geo] using geo_mono (Nat.zero_le n)

theorem CycleProfile.belowTail {M t s : ℕ} (p : CycleProfile M t s) (hM : M ≤ 107) :
    s < tailStart := by
  apply tail_exclusion
  have hb := geometric_total p.single p.rise M
  rw [← p.lengthTotal] at hb
  have hh : 0 ≤ heightLog (p.minimum 0) :=
    Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (p.minimum 0)])
  have h1 : (geo M : ℝ) ≤ (geo 107 : ℝ) := by exact_mod_cast geo_mono hM
  have h2 : 0 ≤ (geo 107 : ℝ) := by exact_mod_cast geo_nonneg 107
  have hr := rhin_minimum (p.minimumPositive 0) p.minimaPositive p.rhin p.gap_minimum
  have hlog := Real.logb_le_logb_of_le (b := 2) (x := (M : ℝ)) (y := 107)
    (by norm_num) (by exact_mod_cast p.minimaPositive) (by exact_mod_cast hM)
  calc
    _ ≤ heightLog (p.minimum 0) * (geo M : ℝ) := hb
    _ ≤ heightLog (p.minimum 0) * (geo 107 : ℝ) := mul_le_mul_of_nonneg_left h1 hh
    _ ≤ _ := by
      rw [mul_comm (heightLog (p.minimum 0))]
      apply mul_le_mul_of_nonneg_left _ h2
      unfold heightLog
      linarith

theorem CycleProfile.minimum_cap {M t s k : ℕ} (p : CycleProfile M t s) {g : ℝ}
    (hM : M ≤ 107) (hg : 0 < g)
    (hg' : g < scaledGap (Real.log 2) (Real.log 3) t s)
    (hc : (107 : ℝ) * (floorHeight : ℝ) < g * (2 : ℝ)^k) :
    p.minimum 0 < 2^k := by
  have hA : (0 : ℝ) < floorHeight := by unfold floorHeight; positivity
  have hm : (0 : ℝ) < p.minimum 0 := by exact_mod_cast p.minimumPositive 0
  have h := hg'.trans (mul_lt_mul_of_pos_left p.gap_minimum hA)
  rw [← mul_div_assoc] at h
  have h := (lt_div_iff₀ hm).1 h
  have hM' : (M : ℝ) ≤ 107 := by exact_mod_cast hM
  have hc' : (floorHeight : ℝ) * 107 < g * 2^k := by simpa only [mul_comm] using hc
  have e := (h.trans_le (mul_le_mul_of_nonneg_left hM' hA.le)).trans hc'
  exact_mod_cast (lt_of_mul_lt_mul_left e hg.le)

theorem CycleProfile.elementary_budget {M t s h b : ℕ} (p : CycleProfile M t s)
    (hM : M ≤ 107) (hb : 1 ≤ b) (hl : b ≤ M - highCount (p.low h) M) :
    (s : ℚ) ≤ (71+h : ℕ) * (geo (108-b) + (b-1 : ℕ)) := by
  let w := geometricWeight ((71+h : ℕ) : ℚ)
  have hr := geometricWeight_mono (k := ((71+h : ℕ) : ℚ)) (by positivity)
  have hw : Monotone (fun i => (w i : ℝ)) := by
    intro a b hab
    change (w a : ℝ) ≤ (w b : ℝ)
    exact_mod_cast hr hab
  have hwn : ∀ n, 0 ≤ (w n : ℝ) := by
    intro n
    have h0 : (0 : ℝ) ≤ (w 0 : ℝ) := by simp [w, geometricWeight]; positivity
    exact h0.trans (hw (Nat.zero_le _))
  have hprice : ∀ i, p.low h i = true → ∀ d,
      (p.length (i+d) : ℝ) ≤ (w d : ℝ) := by
    intro i hi d
    have hn : p.minimum i < 2^(71+h) := by simpa [CycleProfile.low] using hi
    apply (p.rise _).trans
    simpa only [w, geometricWeight, growthR, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
      using geometric_height (L := fun r => heightLog (p.minimum r)) p.single
        (i := i) (heightLog_le_of_lt hn) d
  have he := priced_from_low (a := fun i => (p.length i : ℝ)) hw hwn
    (p.low_at_zero (lt_of_lt_of_le (by omega : 0 < b) hl)) hprice hM hb hl
  rw [← p.lengthTotal, ← prefix_cast, geometric_prefix] at he
  dsimp [w] at he
  simp only [geometricWeight, pow_zero, mul_one, Rat.cast_mul, Rat.cast_natCast] at he
  exact_mod_cast (show (s : ℝ) ≤ (71+(h:ℝ)) *
      ((geo (108-b) : ℝ) + ((b-1 : ℕ) : ℝ)) from by push_cast at he; nlinarith)

theorem CycleProfile.paired_budget_low {M t s : ℕ} (p : CycleProfile M t s)
    (hM : M ≤ 107) (h : 9 ≤ M-highCount (p.low 12) M) :
    (s : ℚ) ≤ pairedBudget 99 + 8*88 := by
  have hm : Monotone (fun i => (gridWeight i : ℝ)) := by
    intro a b hab
    change (gridWeight a : ℝ) ≤ (gridWeight b : ℝ)
    exact_mod_cast gridWeight_mono hab
  have hn : ∀ i, 0 ≤ (gridWeight i : ℝ) := by intro i; exact_mod_cast gridWeight_nonneg i
  have hprice : ∀ i, p.low 12 i = true → ∀ d,
      (p.length (i+d) : ℝ) ≤ (gridWeight d : ℝ) := by
    intro i hi d
    have hx : p.minimum i < 2^(71+12) := by simpa only [CycleProfile.low, decide_eq_true_eq] using hi
    have h0 : heightLog (p.minimum i) ≤ 88 := (heightLog_le_of_lt hx).trans (by norm_num)
    exact (p.rise _).trans (grid_height p.single p.double h0 d)
  have hh := priced_from_low (a := fun i => (p.length i : ℝ)) hm hn
    (p.low_at_zero (lt_of_lt_of_le (by decide) h))
    hprice hM (by decide) h
  rw [← p.lengthTotal, ← prefix_cast, grid_prefix99, gridWeight_at_zero] at hh
  have hcast : (gridBudget 99 : ℝ) ≤ (pairedBudget 99 : ℝ) := by exact_mod_cast grid99_le
  have hfin : (s : ℝ) ≤ ((pairedBudget 99 + 8*88 : ℚ) : ℝ) := by push_cast; norm_num at hh; linarith
  exact_mod_cast hfin

theorem CycleProfile.paired_budget_min {M t s : ℕ} (p : CycleProfile M t s)
    (hM : M ≤ 107) (h : p.minimum 0 < 2^88) : (s : ℚ) ≤ pairedBudget 107 := by
  have hp : ∀ i, (p.length i : ℝ) ≤ (gridWeight i : ℝ) := by
    intro i
    have hi := grid_height p.single p.double (heightLog_le_of_lt h) (i := 0) i
    simp only [Nat.zero_add] at hi
    exact (p.rise i).trans hi
  have hle := Finset.sum_le_sum (s := range M) (fun i _ => hp i)
  change budget (fun i => (p.length i : ℝ)) M ≤ budget (fun i => (gridWeight i : ℝ)) M at hle
  have hn : ∀ i, 0 ≤ (gridWeight i : ℝ) := by intro i; exact_mod_cast gridWeight_nonneg i
  have he := hle.trans (budget_le_mono hn hM)
  rw [← p.lengthTotal, ← prefix_cast, grid_prefix107] at he
  exact (by exact_mod_cast he : (s : ℚ) ≤ gridBudget 107).trans grid107_le

theorem CycleProfile.elementary_budget_min {M t s : ℕ} (p : CycleProfile M t s)
    (hM : M ≤ 107) (h : p.minimum 0 < 2^89) : (s : ℚ) ≤ 89*geo 107 := by
  have hb := geometric_total p.single p.rise M
  rw [← p.lengthTotal] at hb
  have hgeo : (0 : ℝ) ≤ (geo M : ℝ) := by exact_mod_cast geo_nonneg M
  have hmono : (geo M : ℝ) ≤ (geo 107 : ℝ) := by exact_mod_cast geo_mono hM
  exact_mod_cast ((hb.trans (mul_le_mul_of_nonneg_right (heightLog_le_of_lt h) hgeo)).trans
    (mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 89)))

theorem lower_bound_of_profile {M t s : ℕ} (p : CycleProfile M t s) : 108 ≤ M := by
  by_contra hh
  have hm : M ≤ 107 := by omega
  refine hh (lower_bound_from_estimates
    ⟨p.oddPositive, (Real.exp_pos _).trans p.rhin, p.belowTail hm, p.scaled_upper,
      (fun h => M - highCount (p.low h) M), p.scaled_reciprocal,
      ?_, ?_, p.paired_budget_low hm, ?_, ?_⟩ log2_enclosed log3_enclosed)
  · intro h
    simpa using p.elementary_budget hm (h := 3) (b := 57) (by decide) h
  · intro h
    simpa using p.elementary_budget hm (h := 7) (b := 24) (by decide) h
  · intro h
    exact p.paired_budget_min hm (p.minimum_cap hm (by norm_num [bracket5]) h
      (by norm_num [bracket5, floorHeight]))
  · intro h
    exact p.elementary_budget_min hm (p.minimum_cap hm (by norm_num [bracket6]) h
      (by norm_num [bracket6, floorHeight]))

#print axioms lower_bound_of_profile

end Cycle108
