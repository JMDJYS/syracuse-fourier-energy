import Collatz.HercherMinima
import Collatz.TwoRiseCheck
import Tail

/-! Extracted lemmas from Justin Alick, collatz-m-cycles-101-lean,
commit d1895945, Apache-2.0. See LICENSE-Alick. -/

namespace Collatz

open Finset

theorem periodic_add_mul {α : Type*} {f : ℕ → α} {m : ℕ} (hf : ∀ r, f (r + m) = f r)
    (r q : ℕ) : f (r + m * q) = f r := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, hf, ih]


theorem periodic_mod {α : Type*} {f : ℕ → α} {m : ℕ} (hf : ∀ r, f (r + m) = f r) (r : ℕ) :
    f r = f (r % m) := by
  conv_lhs => rw [← Nat.mod_add_div r m]
  exact periodic_add_mul hf _ _

theorem orun_le_logb (n : ℕ) : (orun n : ℝ) ≤ Real.logb 2 ((n : ℝ) + 1) := by
  have h := two_pow_le_of_odd_run (fun t (ht : t < orun n) => odd_of_lt_orun ht)
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast h

/-- The next minimum is at most `T^{k+1} n`. -/
theorem nextMin_le {n : ℕ} (hn : 0 < n) : nextMin n ≤ T^[orun n + 1] n := by
  show T^[orun n + erun n] n ≤ _
  exact iterate_le_of_even_run (erun_pos n) (fun s hs => even_of_lt_erun hn hs)

/-- **Lemma 20 for successive minima**, `log₂(n + 1)` form (step (d)):
`log₂(n_{i+1} + 1) < δ log₂(n_i + 1)`. -/
theorem logb_nextMin_lt {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1) :
    Real.logb 2 ((nextMin n : ℝ) + 1) < Real.logb 2 3 * Real.logb 2 ((n : ℝ) + 1) := by
  have hk := orun_pos hodd
  have hle := nextMin_le hn
  have hlt := succ_iterate_lt_rpow hk (fun t ht => odd_of_lt_orun ht) (orun_spec n)
  have hleR : ((nextMin n : ℕ) : ℝ) ≤ ((T^[orun n + 1] n : ℕ) : ℝ) := by exact_mod_cast hle
  have h1 : ((nextMin n : ℕ) : ℝ) + 1 < ((n : ℝ) + 1) ^ Real.logb 2 3 := by linarith
  rw [← Real.logb_rpow_eq_mul_logb_of_pos (b := 2) (y := Real.logb 2 3)
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]
  exact Real.logb_lt_logb (by norm_num) (by positivity) h1

theorem nextMin_iterate_odd {x : ℕ} (hx : 0 < x) (hodd : x % 2 = 1) (r : ℕ) :
    nextMin^[r] x % 2 = 1 := by
  rcases r with _ | r
  · exact hodd
  · rw [Function.iterate_succ_apply']
    exact nextMin_odd (nextMin_iterate_pos hx r)

def TwoRiseBound (N B : ℕ) : Prop :=
  ∀ n, n % 2 = 1 → n < 2 ^ N → orun n + orun (nextMin n) ≤ B

/-- The block of a local minimum `n` (odd): `n + 1 = 2^k a` with `a` odd, and
`3^k a = 2^ℓ n' + 1`, where `k = orun n`, `ℓ = erun n`, `n' = nextMin n`. -/
theorem block_eq {n : ℕ} (hn : n % 2 = 1) :
    ∃ a, a % 2 = 1 ∧ n + 1 = 2 ^ orun n * a ∧ 3 ^ orun n * a = 2 ^ erun n * nextMin n + 1 := by
  have hn0 : 0 < n := by omega
  obtain ⟨a, ha, hna, hk⟩ := odd_run_form (orun n) n (fun t ht => odd_of_lt_orun ht)
  have hrun := iterate_even_run (n := n) (k := orun n) (erun n)
    (fun s hs => even_of_lt_erun hn0 hs)
  have hnm : T^[orun n + erun n] n = nextMin n := rfl
  rw [hnm, hk] at hrun
  have hev : T^[orun n] n % 2 = 0 := orun_spec n
  rw [hk] at hev
  have h3pos : 1 ≤ 3 ^ orun n * a := Nat.mul_pos (by positivity) ha
  have hodd : (3 ^ orun n * a) % 2 = 1 := by omega
  refine ⟨a, ?_, hna, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · exfalso
    have hd : 2 ∣ 3 ^ orun n * a := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) _
    omega
  · exact h

/-- **The two-rise bound from the kernel-checked arithmetic.** -/
theorem twoRiseBound_of_allPairs {N B : ℕ} (h : TwoRise.AllPairs N B) : TwoRiseBound N B := by
  intro n hn hN
  obtain ⟨a, ha, hna, h1⟩ := block_eq hn
  have hn' : nextMin n % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a', _, hna', _⟩ := block_eq hn'
  have hk1 : 1 ≤ orun n := orun_pos hn
  have hl : 1 ≤ erun n := erun_pos n
  have hle : 2 ^ orun n * a ≤ 2 ^ N := by rw [← hna]; omega
  have hkN : orun n ≤ N := by
    have h2 : 2 ^ orun n ≤ 2 ^ N := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  apply h (orun n) hk1 hkN a (erun n) (orun (nextMin n)) a' ha hle hl
  rw [pow_add, mul_assoc, ← hna', h1]
  ring

theorem logb_one_add_le {u : ℝ} (hu : 0 ≤ u) : Real.logb 2 (1 + u) ≤ 2 * u := by
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := Cycle108.log2_half
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  rw [Real.logb, div_le_iff₀ hpos]
  nlinarith [mul_nonneg hu (le_of_lt (sub_pos.mpr hl2))]

/-- **Two consecutive steps of the chain of minima** (Lemma 1 of the note, twice): with
`x = log₂(n + 1)`, `x'' ≤ x + (δ − 1)(k + k') − 2 + 6/(n + 1)` for the second next minimum. -/
theorem logb_two_step {n : ℕ} (hn : n % 2 = 1) :
    Real.logb 2 ((nextMin (nextMin n) : ℝ) + 1) ≤ Real.logb 2 ((n : ℝ) + 1) +
      (Real.logb 2 3 - 1) * ((orun n + orun (nextMin n) : ℕ) : ℝ) - 2 + 6 / ((n : ℝ) + 1) := by
  obtain ⟨a, _, hna, h1⟩ := block_eq hn
  have hn' : nextMin n % 2 = 1 := nextMin_odd (by omega)
  obtain ⟨a', _, hna', h2⟩ := block_eq hn'
  have hint := TwoRise.two_step_core hna h1 (erun_pos n) hna' h2 (erun_pos _)
  obtain ⟨s, hs⟩ : ∃ s, s = orun n + orun (nextMin n) := ⟨_, rfl⟩
  rw [← hs] at hint ⊢
  have hR : (4 : ℝ) * 2 ^ s * ((nextMin (nextMin n) : ℝ) + 1) ≤ (3 : ℝ) ^ s * ((n : ℝ) + 4) := by
    exact_mod_cast hint
  have hpos1 : (0 : ℝ) < (nextMin (nextMin n) : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hR
  have e1 : Real.logb 2 ((4 : ℝ) * 2 ^ s * ((nextMin (nextMin n) : ℝ) + 1)) =
      2 + s + Real.logb 2 ((nextMin (nextMin n) : ℝ) + 1) := by
    rw [Real.logb_mul (by positivity) hpos1.ne', Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  have e2 : Real.logb 2 ((3 : ℝ) ^ s * ((n : ℝ) + 4)) =
      s * Real.logb 2 3 + Real.logb 2 ((n : ℝ) + 4) := by
    rw [Real.logb_mul (by positivity) hpos2.ne', Real.logb_pow]
  rw [e1, e2] at hlog
  have hq : Real.logb 2 ((n : ℝ) + 4) ≤ Real.logb 2 ((n : ℝ) + 1) + 6 / ((n : ℝ) + 1) := by
    have hn1' : (n : ℝ) + 1 ≠ 0 := hn1.ne'
    have e : (n : ℝ) + 4 = ((n : ℝ) + 1) * (1 + 3 / ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [e, Real.logb_mul hn1.ne' (by positivity)]
    have := logb_one_add_le (show (0 : ℝ) ≤ 3 / ((n : ℝ) + 1) by positivity)
    have e3 : 2 * (3 / ((n : ℝ) + 1)) = 6 / ((n : ℝ) + 1) := by ring
    linarith
  linarith

/-- **The least element of a cycle is a local minimum.** -/
theorem exists_least_rotation {x p : ℕ} (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) :
    ∃ i, IsMinOf (T^[i] x) p ∧ ∀ j, T^[i] x ≤ T^[j] x := by
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image (Finset.range p) (fun j => T^[j] x)
    ⟨0, Finset.mem_range.mpr hp⟩
  have hall : ∀ j, T^[i] x ≤ T^[j] x := by
    intro j
    have hj : T^[j] x = T^[j % p] x :=
      periodic_mod (f := fun j => T^[j] x) (fun r => iterate_add_period hcyc r) j
    rw [hj]
    exact hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ hp))
  refine ⟨i, ⟨?_, ?_⟩, hall⟩
  · by_contra hev
    have hev' : T^[i] x % 2 = 0 := by omega
    have h1 := hall (i + 1)
    rw [Function.iterate_succ_apply', T_even hev'] at h1
    have hpos := iterate_T_pos hx i
    omega
  · by_contra hodd
    have hodd' : T^[p - 1] (T^[i] x) % 2 = 1 := by omega
    have e : T^[p - 1] (T^[i] x) = T^[i + (p - 1)] x := by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    have h1 := hall (i + (p - 1))
    rw [← e] at h1
    have h2 : T (T^[p - 1] (T^[i] x)) = T^[i] x := by
      rw [← Function.iterate_succ_apply' T]
      simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1 ≤ p by omega)]
      exact cycle_rotate hcyc i
    rw [T_odd hodd'] at h2
    have := iterate_T_pos hx i
    omega

theorem cycle_gt_of_verified (hX : ∀ n, 0 < n → n ≤ 2 ^ 71 → Reaches T n 1) {x p : ℕ}
    (hx : 0 < x) (hp : 0 < p) (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    ∀ j, 2 ^ 71 < T^[j] x := by
  intro j
  by_contra h
  exact cycle_not_reaches_one hp hcyc hx1 hx2 j (hX _ (iterate_T_pos hx j) (by omega))

end Collatz
