import Algebra
import Arithmetic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Coverage of the six ranges in Section 4. Dynamical estimates
are explicit hypotheses of the final lemma. -/

namespace Cycle108

def scaledGap (l₂ l₃ : ℝ) (t s : ℕ) : ℝ :=
  (floorHeight : ℝ) * ((t : ℝ) * l₂ - (s : ℝ) * l₃)

theorem bracket_gap {b : Bracket} (hv : b.valid) (hq : 0 < b.q) (hw : 0 < b.w)
    {l₂ l₃ : ℝ}
    (h₂ : (log2Lo : ℝ) ≤ l₂ ∧ l₂ ≤ (log2Hi : ℝ))
    (h₃ : (log3Lo : ℝ) ≤ l₃ ∧ l₃ ≤ (log3Hi : ℝ))
    {t s : ℕ} (hs : 0 < s) (hstop : s < b.stop)
    (hpos : 0 < (t : ℝ) * l₂ - (s : ℝ) * l₃) :
    (b.gap : ℝ) < scaledGap l₂ l₃ t s := by
  rcases hv with ⟨hd, hplus, hminus, hgap⟩
  have hA : (0 : ℝ) < floorHeight := by unfold floorHeight; positivity
  have hpq : (b.p : ℝ) * (log2Lo : ℝ) - (b.q : ℝ) * (log3Hi : ℝ) ≤
      (b.p : ℝ) * l₂ - (b.q : ℝ) * l₃ := by
    linarith [mul_le_mul_of_nonneg_left h₂.1 (show (0:ℝ) ≤ b.p by positivity),
      mul_le_mul_of_nonneg_left h₃.2 (show (0:ℝ) ≤ b.q by positivity)]
  have hrw : (b.r : ℝ) * l₂ - (b.w : ℝ) * l₃ ≤
      (b.r : ℝ) * (log2Hi : ℝ) - (b.w : ℝ) * (log3Lo : ℝ) := by
    linarith [mul_le_mul_of_nonneg_left h₂.2 (show (0:ℝ) ≤ b.r by positivity),
      mul_le_mul_of_nonneg_left h₃.1 (show (0:ℝ) ≤ b.w by positivity)]
  have hd' : (b.p : ℤ) * (b.w : ℤ) = (b.q : ℤ) * (b.r : ℤ) + 1 := by exact_mod_cast hd
  have hh : (b.gap : ℝ) < (floorHeight : ℝ) *
      ((b.p : ℝ) * (log2Lo : ℝ) - (b.q : ℝ) * (log3Hi : ℝ)) := by exact_mod_cast hplus
  have hu : 0 < (b.p : ℝ) * l₂ - (b.q : ℝ) * l₃ := by
    have hg : (0 : ℝ) < (b.gap : ℝ) := by exact_mod_cast hgap
    by_contra hz
    have hle := mul_nonpos_of_nonneg_of_nonpos hA.le (hpq.trans (le_of_not_gt hz))
    linarith
  have hminus' : (b.r : ℝ) * (log2Hi : ℝ) < (b.w : ℝ) * (log3Lo : ℝ) := by
    exact_mod_cast hminus
  have hv' : (b.r : ℝ) * l₂ - (b.w : ℝ) * l₃ < 0 := by linarith
  have hk : (b.p : ℝ) * l₂ - (b.q : ℝ) * l₃ ≤
      (t : ℝ) * l₂ - (s : ℝ) * l₃ := by
    have hk' := unimodular_bound
      (K := ℝ) (p := (b.p : ℤ)) (q := (b.q : ℤ)) (r := (b.r : ℤ)) (w := (b.w : ℤ))
      (t := (t : ℤ)) (s := (s : ℤ)) (u := l₂) (v := l₃)
      (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hd'))
      (by exact_mod_cast hq) (by exact_mod_cast hw) (by exact_mod_cast hs)
      (by unfold Bracket.stop at hstop; exact_mod_cast hstop)
    push_cast at hk'
    exact hk' hu hv' hpos
  exact hh.trans_le (mul_le_mul_of_nonneg_left (hpq.trans hk) hA.le)

theorem low_count {m b l h : ℕ} {g d : ℝ}
    (hm : m ≤ 107) (hb : 1 ≤ b)
    (h0 : g < d) (h1 : d < (l : ℝ) + ((m : ℝ) - l) / 2 ^ h)
    (h2 : ((b - 1 : ℕ) : ℝ) + ((108 - b : ℕ) : ℝ) / 2 ^ h ≤ g)
    (hB : b ≤ 108) : b ≤ l := by
  by_contra hl
  have hL : (l : ℝ) ≤ (b : ℝ) - 1 := by
    have hh : l + 1 ≤ b := by omega
    have hhr : (l : ℝ) + 1 ≤ b := by exact_mod_cast hh
    linarith
  have hM : (m : ℝ) ≤ 107 := by exact_mod_cast hm
  have hd : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  rw [Nat.cast_sub hb, Nat.cast_sub hB] at h2
  push_cast at h2
  have hp : (0 : ℝ) < 2 ^ h := by positivity
  have he : (l : ℝ) + ((m : ℝ) - l) / 2 ^ h ≤
      (b : ℝ) - 1 + (108 - b) / 2 ^ h := by
    apply (mul_le_mul_iff_left₀ hp).1
    have hl' : ((l : ℝ) + ((m : ℝ) - l) / 2 ^ h) * 2 ^ h =
        (l : ℝ) * 2 ^ h + (m - l : ℝ) := by field_simp [hp.ne']
    have hr' : ((b : ℝ) - 1 + (108 - b) / 2 ^ h) * 2 ^ h =
        ((b : ℝ) - 1) * 2 ^ h + (108 - b) := by field_simp [hp.ne']
    rw [hl', hr']
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ) - 1 - l by linarith) (sub_nonneg.mpr hd)]
  exact (not_lt_of_ge h2) (h0.trans (h1.trans_le he))

structure ExclusionEstimates (m t s : ℕ) (l₂ l₃ : ℝ) where
  oddPositive : 0 < s
  gapPositive : 0 < (t : ℝ) * l₂ - (s : ℝ) * l₃
  belowTail : s < tailStart
  gapUpper : scaledGap l₂ l₃ t s < m
  low : ℕ → ℕ
  reciprocalUpper : ∀ h, scaledGap l₂ l₃ t s <
    (low h : ℝ) + ((m : ℝ) - low h) / 2 ^ h
  budget2 : 57 ≤ low 3 → (s : ℚ) ≤ 74 * (geo 51 + 56)
  budget3 : 24 ≤ low 7 → (s : ℚ) ≤ 78 * (geo 84 + 23)
  budget4 : 9 ≤ low 12 → (s : ℚ) ≤ pairedBudget 99 + 8 * 88
  budget5 : (bracket5.gap : ℝ) < scaledGap l₂ l₃ t s →
    (s : ℚ) ≤ pairedBudget 107
  budget6 : (bracket6.gap : ℝ) < scaledGap l₂ l₃ t s → (s : ℚ) ≤ 89 * geo 107

theorem lower_bound_from_estimates {m t s : ℕ} {l₂ l₃ : ℝ}
    (hx : ExclusionEstimates m t s l₂ l₃)
    (h₂ : (log2Lo : ℝ) ≤ l₂ ∧ l₂ ≤ (log2Hi : ℝ))
    (h₃ : (log3Lo : ℝ) ≤ l₃ ∧ l₃ ≤ (log3Hi : ℝ)) : 108 ≤ m := by
  by_contra hn
  have hm : m ≤ 107 := by omega
  let gap (b : Bracket) (hv : b.valid) (hq : 0 < b.q) (hw : 0 < b.w) (h : s < b.stop) :=
    bracket_gap hv hq hw h₂ h₃ hx.oddPositive h hx.gapPositive
  by_cases h1 : s < bracket1.stop
  · have hg := gap bracket1 bracket1_valid (by decide) (by decide) h1
    have h358 : (bracket1.gap : ℝ) = 358 := by norm_num [bracket1]
    have hM : (m : ℝ) ≤ 107 := by exact_mod_cast hm
    linarith [hx.gapUpper]
  by_cases h2' : s < bracket2.stop
  · have hg := gap bracket2 bracket2_valid (by decide) (by decide) h2'
    have hl := low_count (b := 57) hm (by decide) hg (hx.reciprocalUpper 3)
      (by
        change (56 : ℝ) + 51 / 2 ^ 3 ≤ (bracket2.gap : ℝ)
        norm_num [bracket2]) (by decide)
    have hs := (hx.budget2 hl).trans_lt band2_check
    exact h1 (by exact_mod_cast hs)
  by_cases h3' : s < bracket3.stop
  · have hg := gap bracket3 bracket3_valid (by decide) (by decide) h3'
    have hl := low_count (b := 24) hm (by decide) hg (hx.reciprocalUpper 7)
      (by
        change (23 : ℝ) + 84 / 2 ^ 7 ≤ (bracket3.gap : ℝ)
        norm_num [bracket3]) (by decide)
    have hs := (hx.budget3 hl).trans_lt band3_check
    exact h2' (by exact_mod_cast hs)
  by_cases h4' : s < bracket4.stop
  · have hg := gap bracket4 bracket4_valid (by decide) (by decide) h4'
    have hl := low_count (b := 9) hm (by decide) hg (hx.reciprocalUpper 12)
      (by
        change (8 : ℝ) + 99 / 2 ^ 12 ≤ (bracket4.gap : ℝ)
        norm_num [bracket4]) (by decide)
    have hs := (hx.budget4 hl).trans_lt band4_check
    exact h3' (by exact_mod_cast hs)
  by_cases h5 : s < bracket5.stop
  · have hg := gap bracket5 bracket5_valid (by decide) (by decide) h5
    have hs := (hx.budget5 hg).trans_lt band5_check
    exact h4' (by exact_mod_cast hs)
  · have h6 : s < bracket6.stop := by simpa only [stop6] using hx.belowTail
    have hg := gap bracket6 bracket6_valid (by decide) (by decide) h6
    have hs := (hx.budget6 hg).trans_lt band6_check
    exact h5 (by exact_mod_cast hs)

#print axioms lower_bound_from_estimates

end Cycle108
