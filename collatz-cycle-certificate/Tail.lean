import LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Extending the rational check at the tail endpoint to all larger odd counts. -/

namespace Cycle108

theorem log2_half : (1/2 : ℝ) < Real.log 2 := by
  have hr : (1/2 : ℝ) < (logPartial (1/3) 1 : ℝ) := by norm_num [logPartial]
  have h := (log_box_sound (z := (1/3 : ℚ)) (by norm_num) (by norm_num) 1).1
  have e : Real.log (1 + ((1/3 : ℚ) : ℝ)) - Real.log (1 - ((1/3 : ℚ) : ℝ)) =
      Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  exact hr.trans_le (e ▸ h)

theorem logb_three_lt_growth : Real.logb 2 3 < (growth : ℝ) := by
  have hg : (0 : ℝ) < (growth : ℝ) := by norm_num [growth]
  have h := log2_enclosed.1
  have hc : (log3Hi : ℝ) < (growth : ℝ) * (log2Lo : ℝ) := by exact_mod_cast growth_check
  unfold Real.logb
  apply (div_lt_iff₀ (by linarith [log2_half])).2
  exact (log3_enclosed.2.trans_lt hc).trans_le (mul_le_mul_of_nonneg_left h hg.le)

theorem tail_exclusion {s : ℕ}
    (h : (s : ℝ) ≤ (geo 107 : ℝ) *
      (Real.logb 2 107 + 10 + (rhinExponent : ℝ) * Real.logb 2 (s : ℝ))) :
    s < tailStart := by
  by_contra hn
  let Q := (tailStart : ℝ)
  let r := (s : ℝ) / Q
  have hQ : 0 < Q := by norm_num [Q, tailStart]
  have hrs : 1 ≤ r := (le_div_iff₀ hQ).2 (by
    have hle : tailStart ≤ s := by omega
    rw [one_mul]
    dsimp [Q]
    exact_mod_cast hle)
  have hrp : 0 < r := by linarith
  have hmul : Q * r = (s : ℝ) := by dsimp [r]; field_simp
  have hlog := Real.log_le_sub_one_of_pos hrp
  have hpos : 0 < Real.log 2 := by linarith [log2_half]
  have hrlog : Real.logb 2 r ≤ 2*(r-1) := by
    unfold Real.logb
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith)
      (show 0 ≤ 2*Real.log 2-1 by linarith [log2_half])]
  have e : Real.logb 2 (s : ℝ) = Real.logb 2 Q + Real.logb 2 r := by
    rw [← hmul, Real.logb_mul hQ.ne' hrp.ne']
  have h107 : Real.logb 2 107 ≤ 7 := by
    have ht := Real.logb_le_logb_of_le (b := 2) (x := 107) (y := (2 : ℝ)^7)
      (by norm_num) (by norm_num) (by norm_num)
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at ht
  have h83 : Real.logb 2 Q ≤ 83 := by
    have ht := Real.logb_le_logb_of_le (b := 2) (x := Q) (y := (2 : ℝ)^83)
      (by norm_num) hQ (by norm_num [Q, tailStart])
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at ht
  let c := 7 + 10 + (rhinExponent : ℝ) * 83
  have hμ : (0 : ℝ) ≤ (rhinExponent : ℝ) := by norm_num [rhinExponent]
  have hc : 2 * (rhinExponent : ℝ) ≤ c := by norm_num [c, rhinExponent]
  have hmm : Real.logb 2 107 + 10 + (rhinExponent : ℝ) * Real.logb 2 (s : ℝ) ≤ c*r := by
    rw [e]
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left h83 hμ,
      mul_le_mul_of_nonneg_left hrlog hμ,
      mul_nonneg (show (0 : ℝ) ≤ r-1 by linarith) (sub_nonneg.mpr hc)]
  have hg : (0 : ℝ) ≤ (geo 107 : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ geo 107 by decide +kernel)
  have ht : (geo 107 : ℝ) * c < Q := by
    dsimp [Q, c]
    exact_mod_cast tail_check
  have hf := h.trans (mul_le_mul_of_nonneg_left hmm hg)
  have hstrict := mul_lt_mul_of_pos_right ht hrp
  rw [← mul_assoc] at hf
  linarith

/-- The logarithmic upper bound for the least element, obtained from the two
inequalities for the cycle gap. -/
theorem rhin_minimum {m M s : ℕ} {gap : ℝ}
    (hm : 0 < m) (hM : 0 < M)
    (lower : Real.exp (-(rhinExponent : ℝ) * ((rhinShift : ℝ) + Real.log s)) < gap)
    (upper : gap < (M : ℝ) / (m : ℝ)) :
    Real.logb 2 ((m : ℝ)+1) < Real.logb 2 (M : ℝ) + 10 +
        (rhinExponent : ℝ) * Real.logb 2 (s : ℝ) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hl := Real.log_lt_log (Real.exp_pos _) (lower.trans upper)
  rw [Real.log_exp, Real.log_div hMp.ne' hmp.ne'] at hl
  have hc : (rhinExponent : ℝ) * (rhinShift : ℝ) < 9 * (log2Lo : ℝ) := by
    exact_mod_cast rhin_check
  have hl2 : (0 : ℝ) < Real.log 2 := by linarith [log2_half]
  have hg : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ) + 1) hg
  rw [Real.log_mul (by norm_num) hmp.ne'] at hlog
  have ht : Real.log ((m : ℝ) + 1) < Real.log M + 10 * Real.log 2 +
      (rhinExponent : ℝ) * Real.log s := by
    linarith [log2_enclosed.1]
  simp only [Real.logb]
  field_simp [hl2.ne']
  nlinarith

#print axioms tail_exclusion

end Cycle108
