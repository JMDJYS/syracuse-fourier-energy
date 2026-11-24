import Weights

/-! A common budget for one-step growth and the certified chain of two-step caps. -/

namespace Cycle108

def growthR : ℝ := (growth : ℝ)

theorem growthR_pos : 0 < growthR := by norm_num [growthR, growth]

theorem geometric_height {L : ℕ → ℝ} (hs : ∀ i, L (i+1) ≤ growthR * L i)
    {i : ℕ} {k : ℝ} (h : L i ≤ k) (j : ℕ) :
    L (i+j) ≤ k * growthR ^ j := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Nat.add_succ, pow_succ]
    calc
      _ ≤ growthR * L (i+j) := hs _
      _ ≤ growthR * (k * growthR ^ j) := mul_le_mul_of_nonneg_left ih growthR_pos.le
      _ = _ := by ring

theorem grid_height {L : ℕ → ℝ} (hs : ∀ i, L (i+1) ≤ growthR * L i)
    (hpair : ∀ i (j : Fin 17), L i ≤ leanCaps.getD j.val 0 →
      L (i+2) ≤ leanCaps.getD (j.val+1) 0)
    {i : ℕ} (hstart : L i ≤ 88) (d : ℕ) :
    L (i+d) ≤ (gridWeight d : ℝ) := by
  have he : ∀ j ≤ 17, L (i+2*j) ≤ leanCaps.getD j 0 := by
    intro j hj
    induction j with
    | zero => simpa [leanCaps] using hstart
    | succ j ih =>
      simpa only [show i+2*(j+1) = i+2*j+2 by omega] using
        hpair (i+2*j) ⟨j, by omega⟩ (ih (by omega))
  by_cases hd : d < 34
  · rw [gridWeight, if_pos hd]
    have hhalf : d / 2 ≤ 17 := by omega
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · rw [if_pos h, one_mul]
      simpa only [show 2 * (d/2) = d by omega] using he _ hhalf
    · rw [if_neg (by omega)]
      push_cast
      have hx := he (d/2) hhalf
      have hy := (hs (i+2*(d/2))).trans (mul_le_mul_of_nonneg_left hx growthR_pos.le)
      simpa only [show i+2*(d/2)+1 = i+d by omega, growthR] using hy
  · rw [gridWeight, if_neg hd, geometricWeight]
    push_cast
    have h := he 17 (by decide)
    have hz : L (i+34) ≤ 283999 := h
    have hgeom := geometric_height hs hz (d-34)
    simpa only [show i+34+(d-34) = i+d by omega, growthR] using hgeom

theorem geometric_total {L a : ℕ → ℝ} (hs : ∀ i, L (i+1) ≤ growthR * L i)
    (hlen : ∀ i, a i ≤ L i) (M : ℕ) :
    budget a M ≤ L 0 * (geo M : ℝ) := by
  induction M with
  | zero => simp [budget, geo]
  | succ M ih =>
    have hg := geometric_height hs (i := 0) (le_refl (L 0)) M
    simp only [Nat.zero_add] at hg
    have hgeo := geometric_prefix 1 (M+1)
    have hrec : geo (M+1) = geo M + growth ^ M := by
      simpa only [rationalSum, geometric_prefix, geometricWeight, one_mul] using hgeo.symm
    simp only [budget, Finset.sum_range_succ] at ih ⊢
    rw [hrec, Rat.cast_add, Rat.cast_pow, mul_add]
    exact add_le_add ih ((hlen M).trans hg)

#print axioms grid_height

end Cycle108
