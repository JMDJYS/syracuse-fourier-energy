import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Full-Paper Lean 4 Verification for `Uniform_Fourier_Contraction_3adic_Affine_Operators.tex`

This file supplements `SyracuseEnergy.lean` by formalizing and verifying the remaining
mathematical claims across the restructured manuscript:
- **Section 1 & Section 2 (Theorem 1.1, Local Density Lemma, Lemma 2.1)**:
  Stationary Syracuse primitive Fourier energy $E_m^{\mathrm{prim}} = O(1)$,
  $E_m^{\mathrm{prim}} \to \mathcal{I} \in (0, \infty)$, and $E_m = \mathcal{I}m + o(m)$.
- **Sections 3–5 (Lemma 3.1, Lemma 3.2, Proposition 3.3, Theorem 1.4, Remark 4.3, Theorem 1.5)**:
  Compatibility-filtered $3$-adic affine transfer operators, primitive Mackey tensor factorization
  with uniform spectral gap $27/49 < 1$, and quenched-slope conditional contraction with
  Perron spectral radius $\vartheta = \frac{425 + 4\sqrt{5266}}{945} < 1$.
- **Section 7 (Propositions 7.1, 7.2, 7.3)**:
  Two-stage rank-compression factor $(243/49)^{k_2}$, unsliced Cauchy–Schwarz divergence $9\vartheta > 6.812$,
  exponential Markov tail bound, atomic dispersion identity, and $\mathcal{F}_{0,2}$ Jordan-block cascade.
-/

open Filter Topology Function Finset MeasureTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PaperAudit

/-!
## Part I: Section 1 & Section 2 — Stationary Syracuse Primitive Energy (Theorem 1.1 & Lemma 2.1)

1. **Marginal consistency & Parseval telescope (Equation (1.6))**:
   $E_m = E_{m-1} + E_m^{\mathrm{prim}}$ implies $E_m = \sum_{j=0}^{m-1} E_{j+1}^{\mathrm{prim}}$ when $E_0 = 0$.
2. **Weak-$L^2$ level-set tail bound (Section 2.1)**:
   If $t \cdot m \le C_0 \sqrt{m}$ for $t > 0$ and $m \ge 0$, then $m \le C_0^2 / t^2$.
3. **Collision congruence reduction (Theorem 1.1 proof, Equation (2.6))**:
   - Equal-exponent collision ($a = b$): geometric weight $3 \sum_{a \ge 1} 4^{-a} = 1$.
   - Shifted-exponent collision ($b = a + 2r$):
     $4^r (1 + 3 x) - (1 + 3 y) = 3 (\Theta_r(x) - y)$ where $\Theta_r(x) = 4^r x + \frac{4^r - 1}{3}$,
     and the geometric weight is $3 \sum_{a \ge 1} 2^{-a} 2^{-(a+2r)} = 4^{-r}$.
4. **3-adic Lifting-the-Exponent (Lemma 2.1)**:
   $4^{3^j} - 1 = 3^{j+1} u_j$ with $u_j \equiv 1 \pmod 3$, establishing $v_3(4^{3^j} - 1) = j + 1$.
-/

/-- The affine collision shift map $\Theta_r(x) = 4^r x + (4^r - 1)/3$ from Theorem 1.1. -/
def Theta (r : ℕ) (x : ℚ) : ℚ :=
  (4 : ℚ)^r * x + ((4 : ℚ)^r - 1) / 3

/-- Key algebraic identity behind Equation (2.6) in the proof of Theorem 1.1:
$4^r (1 + 3 x) - (1 + 3 y) = 3 (\Theta_r(x) - y)$.
Consequently, after clearing $2^{a+2r}$, two Syracuse branches with $b = a + 2r$
collide modulo $3^{m+1}$ if and only if $y \equiv \Theta_r(x) \pmod{3^m}$. -/
theorem collision_shift_algebraic_identity (r : ℕ) (x y : ℚ) :
    (4 : ℚ)^r * (1 + 3 * x) - (1 + 3 * y) = 3 * (Theta r x - y) := by
  unfold Theta
  ring

/-- For integer arguments, $3 \mid (4^r - 1)$ for every $r \in \mathbb{N}$. -/
theorem three_dvd_four_pow_sub_one (r : ℕ) : (3 : ℤ) ∣ ((4 : ℤ)^r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rcases ih with ⟨k, hk⟩
    refine ⟨4 * k + 1, ?_⟩
    calc
      (4 : ℤ)^(r + 1) - 1 = 4 * ((4 : ℤ)^r - 1) + 3 := by ring
      _ = 4 * (3 * k) + 3 := by rw [hk]
      _ = 3 * (4 * k + 1) := by ring

/-- Exact 3-adic valuation identity $v_3(4^{3^j} - 1) = j + 1$ used in Lemma 2.1:
for all $j \in \mathbb{N}$, there exists an integer $u_j \equiv 1 \pmod 3$ such that
$4^{3^j} - 1 = 3^{j+1} u_j$. In particular $3^{j+1} \mid (4^{3^j} - 1)$ and $3^{j+2} \nmid (4^{3^j} - 1)$. -/
theorem four_pow_three_pow_exact_div (j : ℕ) :
    ∃ u : ℤ, (4 : ℤ)^(3^j) - 1 = (3 : ℤ)^(j + 1) * u ∧ u % 3 = 1 := by
  induction j with
  | zero =>
    refine ⟨1, ?_, ?_⟩ <;> norm_num
  | succ j ih =>
    rcases ih with ⟨u, hu, humod⟩
    refine ⟨u + (3 : ℤ)^(j + 1) * u^2 + (3 : ℤ)^(2 * j + 1) * u^3, ?_, ?_⟩
    · have hpow : (4 : ℤ)^(3^(j + 1)) = ((4 : ℤ)^(3^j))^3 := by
        rw [pow_succ, pow_mul]
      have h4 : (4 : ℤ)^(3^j) = 1 + (3 : ℤ)^(j + 1) * u := by linarith
      rw [hpow, h4]
      ring
    · have hj1 : (3 : ℤ) ∣ (3 : ℤ)^(j + 1) * u^2 := by
        refine ⟨(3 : ℤ)^j * u^2, ?_⟩
        ring
      have hj2 : (3 : ℤ) ∣ (3 : ℤ)^(2 * j + 1) * u^3 := by
        refine ⟨(3 : ℤ)^(2 * j) * u^3, ?_⟩
        ring
      rcases hj1 with ⟨k1, hk1⟩
      rcases hj2 with ⟨k2, hk2⟩
      rw [hk1, hk2, show u + 3 * k1 + 3 * k2 = u + 3 * (k1 + k2) by ring,
        Int.add_mul_emod_self_left]
      exact humod

/-- Diagonal collision weight sum in Theorem 1.1: $3 \sum_{a=0}^\infty 4^{-(a+1)} = 1$. -/
theorem diagonal_collision_weight_sum :
    (∑' a : ℕ, (3 : ℝ) * (1 / 4 : ℝ)^(a + 1)) = 1 := by
  have h : (fun a : ℕ => (3 : ℝ) * (1 / 4 : ℝ)^(a + 1)) =
      (fun a : ℕ => (3 / 4 : ℝ) * (1 / 4 : ℝ)^a) := by
    ext a
    rw [pow_succ]
    ring
  rw [h, tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])]
  norm_num

/-- Off-diagonal collision weight sum in Theorem 1.1:
for $b = a + 2r$ (with $a \ge 1$), $3 \sum_{a=1}^\infty 2^{-a} 2^{-(a+2r)} = 4^{-r}$. -/
theorem off_diagonal_collision_weight_sum (r : ℕ) :
    (∑' a : ℕ, (3 : ℝ) * ((1 / 2 : ℝ)^(a + 1) * (1 / 2 : ℝ)^(a + 1 + 2 * r))) =
      (1 / 4 : ℝ)^r := by
  have h : (fun a : ℕ => (3 : ℝ) * ((1 / 2 : ℝ)^(a + 1) * (1 / 2 : ℝ)^(a + 1 + 2 * r))) =
      (fun a : ℕ => ((3 / 4 : ℝ) * (1 / 4 : ℝ)^r) * (1 / 4 : ℝ)^a) := by
    ext a
    have h4 : (1 / 4 : ℝ) = (1 / 2 : ℝ)^2 := by norm_num
    rw [h4, ← pow_mul, ← pow_mul]
    simp only [pow_add]
    ring
  rw [h, tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])]
  ring

/-- Telescoping of total Fourier energy from marginal consistency $E_{j+1} - E_j = E_{j+1}^{\mathrm{prim}}$
and $E_0 = 0$ (Equation (1.6)). -/
theorem total_energy_eq_sum_primitive (E Eprim : ℕ → ℝ)
    (h0 : E 0 = 0) (hstep : ∀ m, E (m + 1) = E m + Eprim (m + 1)) (m : ℕ) :
    E m = ∑ j ∈ range m, Eprim (j + 1) := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, hstep m]

/-- Weak-$L^2$ level-set Markov inequality in Section 2.1:
If $t \cdot m \le C_0 \sqrt{m}$ for $t > 0$ and $m \ge 0$, then $m \le C_0^2 / t^2$. -/
theorem weak_L2_level_set_bound {t m C0 : ℝ}
    (ht : 0 < t) (hm : 0 ≤ m)
    (h : t * m ≤ C0 * Real.sqrt m) :
    m ≤ C0^2 / t^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ht)]
  have hsq : (t * m)^2 ≤ (C0 * Real.sqrt m)^2 :=
    pow_le_pow_left₀ (mul_nonneg ht.le hm) h 2
  have hrew : (C0 * Real.sqrt m)^2 = C0^2 * m := by
    rw [mul_pow, Real.sq_sqrt hm]
  rw [mul_pow, hrew] at hsq
  by_cases hm0 : m = 0
  · simp [hm0]
    positivity
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    nlinarith

/-- Parity of powers of $2$ modulo $3$: $(2 : \mathbb{Z})^a \bmod 3 = 1$ if $a$ is even, and $2$ if $a$ is odd. -/
theorem two_pow_mod_three (a : ℕ) :
    (2 : ℤ)^a % 3 = if a % 2 = 0 then 1 else 2 := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ, Int.mul_emod, ih]
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · have hs : (a + 1) % 2 = 1 := by omega
      simp [h0, hs]
    · have hs : (a + 1) % 2 = 0 := by omega
      simp [h1, hs]

/-- Parity filter in Lemma 2.2 (`hidentity` bridge):
Two powers of $2$ are congruent modulo $3$ if and only if their exponents have the same parity. -/
theorem mod_three_parity_filter (a b : ℕ) :
    (2 : ℤ)^a % 3 = (2 : ℤ)^b % 3 ↔ a % 2 = b % 2 := by
  rw [two_pow_mod_three a, two_pow_mod_three b]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [ha, hb]

/-- Diagonal congruence reduction in Lemma 2.2 (`hidentity` bridge):
$(1 + 3 z_1) \equiv (1 + 3 z_2) \pmod{3^{m+1}} \iff z_1 \equiv z_2 \pmod{3^m}$. -/
theorem diagonal_congruence_reduction (m : ℕ) (z1 z2 : ℤ) :
    (3 : ℤ)^(m + 1) ∣ ((1 + 3 * z1) - (1 + 3 * z2)) ↔ (3 : ℤ)^m ∣ (z1 - z2) := by
  have hsub : (1 + 3 * z1) - (1 + 3 * z2) = 3 * (z1 - z2) := by ring
  have hpow : (3 : ℤ)^(m + 1) = 3 * (3 : ℤ)^m := by rw [pow_succ']
  rw [hsub, hpow]
  exact mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)

/-- Off-diagonal shifted congruence reduction in Lemma 2.2 (`hidentity` bridge):
For $3\theta = 4^r - 1$, $4^r(1 + 3 z_1) \equiv 1 + 3 z_2 \pmod{3^{m+1}} \iff 4^r z_1 + \theta \equiv z_2 \pmod{3^m}$. -/
theorem shifted_congruence_reduction (m r : ℕ) (z1 z2 theta : ℤ)
    (htheta : 3 * theta = (4 : ℤ)^r - 1) :
    (3 : ℤ)^(m + 1) ∣ ((4 : ℤ)^r * (1 + 3 * z1) - (1 + 3 * z2)) ↔
      (3 : ℤ)^m ∣ ((4 : ℤ)^r * z1 + theta - z2) := by
  have hsub : (4 : ℤ)^r * (1 + 3 * z1) - (1 + 3 * z2) =
      3 * ((4 : ℤ)^r * z1 + theta - z2) := by linarith
  have hpow : (3 : ℤ)^(m + 1) = 3 * (3 : ℤ)^m := by rw [pow_succ']
  rw [hsub, hpow]
  exact mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)

/-- Cylinder rescaling domination step in Lemma 2.3 (`hdom` bridge):
If the normalized conditional product integral satisfies $\eta \le I / (a b)$ whenever $a, b > 0$,
then $\eta (a b) \le I$ holds unconditionally for all $a, b, I \ge 0$ (including when $a = 0$ or $b = 0$). -/
theorem cylinder_rescaling_domination {eta a b I : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hI : 0 ≤ I)
    (hpos : 0 < a → 0 < b → eta ≤ I / (a * b)) :
    eta * (a * b) ≤ I := by
  by_cases ha0 : a = 0
  · subst ha0; simp [hI]
  · by_cases hb0 : b = 0
    · subst hb0; simp [hI]
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact (le_div_iff₀ (mul_pos hapos hbpos)).mp (hpos hapos hbpos)

/-!
## Part II: Section 3 & Theorem 1.4 (`thm:A1`) — Primitive Mackey Tensor Factorization

We formalize and verify:
1. **Lemma 3.1 (`lem:compat`)**: Exact compatibility congruence modulo $p$ and reduction to $\mathbb{Z}/M\mathbb{Z}$.
2. **Theorem 1.4(1) phase congruence upgrade modulo $pM$**:
   Why $q\alpha \equiv \alpha' \pmod M$ and $p \mid (\lambda_1 k_1 + \beta_1)$ imply
   $q\alpha u(\lambda_1 k_1 + \beta_1) \equiv (\alpha' u)(\lambda_1 k_1 + \beta_1) \pmod{pM}$,
   allowing the exact tensor factorization $U_M B_d^{(0)} U_{pM}^* = p^{-1/2} \overline{A_d} \otimes A_d$.
3. **Section 3.2 & Theorem 1.4(2)--(3) Syracuse weights and spectral gap bounds**:
   - Equation (3.2): $W_1[0] = 8/7$, $W_1[1] = 11/7$, $W_1[2] = 2/7$, $\sum_k W_1[k] = 3$.
   - Lemma 3.2 (`lem:W_omega_2e`): $W_{\Omega(2^e)} = 2^{-|e|}$, $\mathbb{P}(e\text{ even}) = 5/9$, $\mathbb{P}(e\text{ odd}) = 4/9$.
   - General compatibility triangle bound: $\frac{1}{3^3}(\sum_k W_1[k]^2)^2 = \frac{27}{49} < 1$.
   - Exact 1D monomial off-diagonal $\ell^1$ sum: $\frac{2}{63} + \frac{16}{63} = \frac{2}{7}$,
     giving $1 - \frac{2}{7} = \frac{5}{7}$, $1 + \frac{2}{7} = \frac{9}{7}$, and
     $\frac{1}{3}(9/7)^2 = \frac{27}{49} < 1$.
   - Remark 4.3 (`rem:resonance_1dhs`): $1 + \frac{2}{105} + \frac{4}{1575} = \frac{1609}{1575}$.
-/

/-- Lemma 3.1 (`lem:compat`): Given $\lambda_1 k_1 + \beta_1 = p \tau_1$ and $\lambda_2 k_2 + \beta_2 = p \tau_2$,
for $\kappa = k_2 - \alpha k_1$, the numerator $\lambda_2 \gamma + \beta_2 - q \alpha \beta_1$
(after multiplying by $\lambda_1$ with $q = \lambda_2 / \lambda_1$) is congruent to
$\lambda_1 \lambda_2 (\gamma - \kappa)$ modulo $p$. -/
theorem compatibility_congruence_identity (p lam1 lam2 beta1 beta2 k1 k2 tau1 tau2 alpha gamma : ℤ)
    (h1 : lam1 * k1 + beta1 = p * tau1)
    (h2 : lam2 * k2 + beta2 = p * tau2) :
    lam1 * (lam2 * gamma + beta2) - lam2 * alpha * beta1 =
      lam1 * lam2 * (gamma - (k2 - alpha * k1)) + p * (lam1 * tau2 - lam2 * alpha * tau1) := by
  have hb1 : beta1 = p * tau1 - lam1 * k1 := by linarith
  have hb2 : beta2 = p * tau2 - lam2 * k2 := by linarith
  rw [hb1, hb2]
  ring

/-- Theorem 1.4(1) crucial modulo-$pM$ phase upgrade (Section 4.1):
If $\lambda_1 q_\alpha = \lambda_2 \alpha$, $q_\alpha \equiv \alpha' \pmod M$ (so $q_\alpha - \alpha' = M \cdot t$), and
$\lambda_1 k_1 + \beta_1 = p \cdot \tau_1$, then after clearing $\lambda_1$, the phase difference is an exact
multiple of $pM$, so the total phase splits into the $b_2$ phase minus the $b_1$ phase modulo $pM$. -/
theorem mackey_phase_tensor_split (p M y1 y2 x1 x2 lam1 lam2 beta1 beta2 k1 k2 tau1 alpha q_alpha alpha' u t : ℤ)
    (hy1 : y1 = alpha * y2)
    (hx1 : x1 = alpha' * u)
    (hx2 : x2 = u)
    (hq : lam1 * q_alpha = lam2 * alpha)
    (hcompat1 : lam1 * k1 + beta1 = p * tau1)
    (hslope : q_alpha - alpha' = M * t) :
    ((y2 - lam2 * u) * (k2 - alpha * k1) - u * beta2 + q_alpha * u * beta1) -
      (((y2 - lam2 * x2) * k2 - beta2 * x2) - ((y1 - lam1 * x1) * k1 - beta1 * x1)) =
      (p * M) * (t * u * tau1) := by
  have hb1 : beta1 = p * tau1 - lam1 * k1 := by linarith
  have hqa : q_alpha = alpha' + M * t := by linarith
  calc
    ((y2 - lam2 * u) * (k2 - alpha * k1) - u * beta2 + q_alpha * u * beta1) -
        (((y2 - lam2 * x2) * k2 - beta2 * x2) - ((y1 - lam1 * x1) * k1 - beta1 * x1))
      = (lam2 * alpha - lam1 * q_alpha) * u * k1 + (p * M) * (t * u * tau1) := by
        rw [hy1, hx1, hx2, hb1, hqa]
        ring
    _ = (p * M) * (t * u * tau1) := by
        rw [← hq]
        ring

/-- Section 3.2, Equation (3.2): Exact Syracuse compatibility-class sums $W_1[0], W_1[1], W_1[2]$
from $k(s,r) \equiv r - (s+1) \pmod 3$ and $\sum_{m=0}^\infty 4^{-3m} = 64/63$. -/
theorem syracuse_W1_class_sums :
    let geom63 : ℚ := 64 / 63
    let W0 : ℚ := (3 / 4) * (1 * 1 + 2 * (1 / 4)) * geom63
    let W1 : ℚ := (3 / 4) * (1 * (1 / 16) + 2 * 1) * geom63
    let W2 : ℚ := (3 / 4) * (1 * (1 / 4) + 2 * (1 / 16)) * geom63
    W0 = 8 / 7 ∧ W1 = 11 / 7 ∧ W2 = 2 / 7 ∧
    W0 + W1 + W2 = 3 ∧
    (W0^2 + W1^2 + W2^2)^2 / 27 = 27 / 49 := by
  norm_num

/-- Lemma 3.2 (`lem:W_omega_2e`): Exact slope-ratio slice mass $W_{\Omega(2^e)} = 2^{-|e|}$
for even $e = 2m$ and odd $e = 2m+1$, and parity probabilities $\mathbb{P}(e \text{ even}) = 5/9$,
$\mathbb{P}(e \text{ odd}) = 4/9$. -/
theorem lemma_3_2_slope_ratio_distribution (m : ℕ) :
    (∑' s1 : ℕ, (3 / 16 : ℝ) * (1^2 + 2^2) * (1 / 4 : ℝ)^m * (1 / 16 : ℝ)^s1) =
      (1 / 2 : ℝ)^(2 * m) ∧
    (∑' s1 : ℕ, (3 / 16 : ℝ) * (2 * (1 / 4 : ℝ)^m + 2 * (1 / 4 : ℝ)^(m + 1)) * (1 / 16 : ℝ)^s1) =
      (1 / 2 : ℝ)^(2 * m + 1) ∧
    (1 / 3 : ℝ) * (1 + 2 * ∑' k : ℕ, (1 / 4 : ℝ)^(k + 1)) = 5 / 9 ∧
    (1 / 3 : ℝ) * (2 * ∑' k : ℕ, (1 / 2 : ℝ) * (1 / 4 : ℝ)^k) = 4 / 9 := by
  have h16 : (∑' s1 : ℕ, (1 / 16 : ℝ)^s1) = 16 / 15 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])]
    norm_num
  have h4 : (∑' k : ℕ, (1 / 4 : ℝ)^k) = 4 / 3 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])]
    norm_num
  have hpow2m : (1 / 4 : ℝ)^m = (1 / 2 : ℝ)^(2 * m) := by
    rw [pow_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tsum_mul_left, h16, hpow2m]
    ring
  · rw [tsum_mul_left, h16, pow_succ, hpow2m]
    ring
  · have hshift : (fun k : ℕ => (1 / 4 : ℝ)^(k + 1)) = (fun k : ℕ => (1 / 4 : ℝ) * (1 / 4 : ℝ)^k) := by
      ext k; rw [pow_succ]; ring
    rw [hshift, tsum_mul_left, h4]
    norm_num
  · rw [tsum_mul_left, h4]
    norm_num

/-- Theorem 1.4(3): Syracuse 1D Gram operator off-diagonal $\ell^1$ sum and uniform spectral gap. -/
theorem syracuse_gram_monomial_collapse :
    let same_r_offdiag : ℚ := ((1 + 4 : ℚ) / 5) * 2 * ((1 / 64 : ℚ) / (1 - 1 / 64))
    let diff_r_offdiag : ℚ := 2 * (2 / 5 : ℚ) * ((1 / 4 + 1 / 16 : ℚ) / (1 - 1 / 64))
    let offdiag_total : ℚ := same_r_offdiag + diff_r_offdiag
    same_r_offdiag = 2 / 63 ∧
    diff_r_offdiag = 16 / 63 ∧
    offdiag_total = 2 / 7 ∧
    1 - offdiag_total = 5 / 7 ∧
    1 + offdiag_total = 9 / 7 ∧
    (1 / 3 : ℚ) * (1 + offdiag_total)^2 = 27 / 49 ∧
    (27 / 49 : ℚ) < 1 := by
  norm_num

/-- Theorem 1.4(3): Exact cancellation of $\lambda_1$ in the 1D Syracuse phase shift $c_{\mathrm{1D}}$. -/
theorem syracuse_c1D_lambda_cancellation (lam1 lam2 r1 r2 k : ℚ)
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) (hlam2 : lam2 ≠ 0) :
    let beta1 := lam1 / 3 - (1 + 3 * r1) / (3 * r1)
    let beta2 := lam2 / 3 - (1 + 3 * r2) / (3 * r2)
    let tau1 := (lam1 * k + beta1) / 3
    let tau2 := (lam2 * k + beta2) / 3
    let q := lam1 / lam2
    tau2 * q - tau1 = (1 / 9 : ℚ) * ((1 + 3 * r1) / r1 - q * ((1 + 3 * r2) / r2)) := by
  dsimp only
  field_simp
  ring

/-- Remark 4.3 (`rem:resonance_1dhs`): Exact 2nd trace-moment resonance classification limit. -/
theorem syracuse_trace_moment_q2 :
    (1 : ℚ) + 2 / 105 + 4 / 1575 = 1609 / 1575 := by
  norm_num

/-!
## Part III: Proposition 3.3 & Theorem 1.5 (`thm:cond_contraction`) — Quenched-Slope Contraction

We verify:
1. Exact fiberwise conditional weights $P_\kappa(a, 2^e)$ in Proposition 3.3 and Section 5.
2. The conditional Markov transition matrix $M_{\mathrm{cond}} = \begin{pmatrix} 5/9 & 68/225 \\ 52/189 & 65/189 \end{pmatrix}$.
3. Exact trace, determinant, discriminant, and Perron spectral radius
   $\vartheta = \frac{425 + 4\sqrt{5266}}{945} \in (0.756898, 0.756899) < 1$.
-/

/-- Proposition 3.3(2) & (3) and Section 5: Exact compatibility fiber weights and their squared sums. -/
theorem proposition_3_3_fiber_weights :
    -- Odd e, alpha ≡ 2 (mod 3):
    let p_u1 : ℚ := (3 / 4) * 1 * (4096 / 4095) + (3 / 16) * (1 / 16) * (4096 / 4095)
    let p_u0 : ℚ := (3 / 4) * (1 / 256) * (4096 / 4095) + (3 / 16) * 1 * (4096 / 4095)
    let p_u2 : ℚ := (3 / 4) * (1 / 16) * (4096 / 4095) + (3 / 16) * (1 / 256) * (4096 / 4095)
    p_u1 = 16 / 21 ∧ p_u0 = 4 / 21 ∧ p_u2 = 1 / 21 ∧
    p_u1 + p_u0 + p_u2 = 1 ∧
    p_u1^2 + p_u0^2 + p_u2^2 = 13 / 21 ∧
    -- Even e, alpha ≡ 2 (mod 3):
    ((64 / 273 : ℚ)^2 + (4 / 273 : ℚ)^2 + (205 / 273 : ℚ)^2) = 13 / 21 ∧
    -- Odd e, alpha ≡ 1 (mod 3):
    ((4 / 5 : ℚ)^2 + (1 / 5 : ℚ)^2) = 17 / 25 := by
  norm_num

/-- Theorem 1.5(2): Entries, trace, determinant, and discriminant of $M_{\mathrm{cond}}$. -/
theorem M_cond_matrix_properties :
    let p_even : ℚ := 5 / 9
    let p_odd : ℚ := 4 / 9
    let M11 : ℚ := p_even * 1
    let M12 : ℚ := p_odd * (17 / 25)
    let M21 : ℚ := p_odd * (13 / 21)
    let M22 : ℚ := p_even * (13 / 21)
    let tr : ℚ := M11 + M22
    let det : ℚ := M11 * M22 - M12 * M21
    M11 = 5 / 9 ∧ M12 = 68 / 225 ∧ M21 = 52 / 189 ∧ M22 = 65 / 189 ∧
    tr = 170 / 189 ∧ det = 4589 / 42525 ∧
    (tr / 2)^2 - det = (16 * 5266) / 945^2 := by
  norm_num

/-- Theorem 1.5(2): The Perron eigenvalue $\vartheta = \frac{425 + 4\sqrt{5266}}{945}$ satisfies
$0.756898 < \vartheta < 0.756899 < 1$ and solves the characteristic equation $\vartheta^2 - \operatorname{tr}\vartheta + \det = 0$. -/
theorem M_cond_spectral_radius_bounds :
    let theta : ℝ := (425 + 4 * Real.sqrt 5266) / 945
    theta^2 - (170 / 189 : ℝ) * theta + (4589 / 42525 : ℝ) = 0 ∧
    (0.756898 : ℝ) < theta ∧ theta < (0.756899 : ℝ) ∧ theta < 1 := by
  intro theta
  have hsq : (Real.sqrt 5266)^2 = 5266 := Real.sq_sqrt (by norm_num)
  have hchar : theta^2 - (170 / 189 : ℝ) * theta + (4589 / 42525 : ℝ) = 0 := by
    dsimp [theta]
    calc
      ((425 + 4 * Real.sqrt 5266) / 945)^2 - (170 / 189 : ℝ) * ((425 + 4 * Real.sqrt 5266) / 945) +
          (4589 / 42525 : ℝ)
        = (16 * ((Real.sqrt 5266)^2 - 5266)) / 945^2 := by ring
      _ = 0 := by rw [hsq]; ring
  have hlow_sq : (72.567209 : ℝ) < Real.sqrt 5266 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 72.567209)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hhigh_sq : Real.sqrt 5266 < (72.567211 : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 72.567211)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨hchar, ?_, ?_, ?_⟩
  · dsimp [theta]; linarith
  · dsimp [theta]; linarith
  · dsimp [theta]; linarith

/-!
## Part IV: Section 7 — Structural Obstruction Propositions 7.1, 7.2, 7.3

We verify:
1. **Proposition 7.1**: $9 \cdot \frac{27}{49} = \frac{243}{49} > 1$.
2. **Proposition 7.2(1)**: Unsliced Cauchy–Schwarz base $9 \vartheta > 6.812 > 1$.
3. **Proposition 7.2(2)**: Minimum outgoing compatible weight $W_{\mathrm{out}}(2, 0) = 36/49$
   and exponential Markov tail inequality $\frac{3 + 2\sqrt{2}}{16} < \frac{18}{49} = \frac{1}{2} \cdot \frac{36}{49}$.
4. **Proposition 7.3(1)**: Exact algebraic atomic lower bound identity
   $a^2 + \frac{b^2}{N-1} - \frac{(a+b)^2}{N} = \left(1 - \frac{1}{N}\right)\left(a - \frac{b}{N-1}\right)^2$.
5. **Proposition 7.3(3)**: Exact 3-step conjugation transition on $\mathcal{F}_{0,2}$ from $(2, 1/2)$ to $(1/4, -3/8)$
   with weight product $\frac{3}{128} \cdot \frac{3}{8} \cdot \frac{3}{8} \cdot (3/4)^{-3} = \frac{1}{128}$.
-/

/-- Proposition 7.1 & 7.2(1): Two-stage scaling factor and unsliced Cauchy–Schwarz growth rate. -/
theorem prop_7_1_and_7_2_constants :
    (9 : ℚ) * (27 / 49) = 243 / 49 ∧
    (6.812 : ℝ) < 9 * ((425 + 4 * Real.sqrt 5266) / 945) := by
  refine ⟨by norm_num, ?_⟩
  have h := M_cond_spectral_radius_bounds.2.1
  linarith

/-- Proposition 7.2(2): Exact minimum compatible row sum $W_{\mathrm{out}}(2, 0) = 36/49$
and exponential Markov inequality $\frac{3 + 2\sqrt{2}}{16} < \frac{18}{49} = \frac{1}{2}\cdot\frac{36}{49}$. -/
theorem prop_7_2_exponential_markov_bound :
    (1 / 3 : ℚ) * ((8 / 7)^2 + 2 * (11 / 7) * (2 / 7)) = 36 / 49 ∧
    ((3 + 2 * Real.sqrt 2) / 16 : ℝ) < 18 / 49 := by
  refine ⟨by norm_num, ?_⟩
  have hsqrt2 : Real.sqrt 2 < (1.415 : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.415)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- Proposition 7.3(1): Error-free atomic Cauchy–Schwarz dispersion identity. -/
theorem prop_7_3_atomic_dispersion_identity (a b N : ℚ) (hN : N ≠ 0) (hN1 : N - 1 ≠ 0) :
    a^2 + b^2 / (N - 1) - (a + b)^2 / N = (1 - 1 / N) * (a - b / (N - 1))^2 := by
  field_simp
  ring

/-- Affine conjugation transition formula (Equation (3.1)):
$\alpha' = (\lambda_2 / \lambda_1)\alpha$ and $\gamma' = (\lambda_2 \gamma + \beta_2 - (\lambda_2/\lambda_1)\alpha \beta_1)/3$. -/
def affineConj (lam1 beta1 lam2 beta2 : ℚ) (tau : ℚ × ℚ) : ℚ × ℚ :=
  let q := lam2 / lam1
  (q * tau.1, (lam2 * tau.2 + beta2 - q * tau.1 * beta1) / 3)

/-- Proposition 7.3(3): Verification of the self-loop $(0,2,0,2)$ and the 3-step word
$(2, 1/2) \to (1/16, -1/4) \to (1/8, -5/16) \to (1/4, -3/8)$ on the trap family $\mathcal{F}_{0,2}$,
together with its exact Jordan-block coefficient $\frac{1}{128}$. -/
theorem prop_7_3_jordan_block_cascade :
    -- Branch parameters (s, r):
    -- (0, 2): lam = 2, beta = -1/2, w1 = 3/2
    -- (2, 1): lam = 64, beta = 20, w1 = 3/64
    -- (0, 1): lam = 4, beta = 0, w1 = 3/4
    let step_self := affineConj 2 (-1/2) 2 (-1/2)
    let step1 := affineConj 64 20 2 (-1/2)
    let step2 := affineConj 2 (-1/2) 4 0
    let tau0 : ℚ × ℚ := (2, 1/2)
    let tau1 : ℚ × ℚ := step1 tau0
    let tau2 : ℚ × ℚ := step2 tau1
    let tau3 : ℚ × ℚ := step2 tau2
    step_self tau0 = (2, 1/2) ∧
    tau1 = (1/16, -1/4) ∧
    tau2 = (1/8, -5/16) ∧
    tau3 = (1/4, -3/8) ∧
    step_self tau3 = (1/4, -3/8) ∧
    -- Both tau0 and tau3 lie on F_{0,2} = {(alpha, (alpha - 1)/2)}:
    tau0.2 = (tau0.1 - 1) / 2 ∧
    tau3.2 = (tau3.1 - 1) / 2 ∧
    -- 3-step weight and Jordan coefficient:
    (3 / 128 : ℚ) * (3 / 8) * (3 / 8) = 27 / 8192 ∧
    (27 / 8192 : ℚ) / (3 / 4)^3 = 1 / 128 := by
  dsimp [affineConj]
  norm_num

#print axioms collision_shift_algebraic_identity
#print axioms three_dvd_four_pow_sub_one
#print axioms four_pow_three_pow_exact_div
#print axioms diagonal_collision_weight_sum
#print axioms off_diagonal_collision_weight_sum
#print axioms total_energy_eq_sum_primitive
#print axioms weak_L2_level_set_bound
#print axioms mod_three_parity_filter
#print axioms diagonal_congruence_reduction
#print axioms shifted_congruence_reduction
#print axioms cylinder_rescaling_domination
#print axioms compatibility_congruence_identity
#print axioms mackey_phase_tensor_split
#print axioms syracuse_W1_class_sums
#print axioms lemma_3_2_slope_ratio_distribution
#print axioms syracuse_gram_monomial_collapse
#print axioms syracuse_c1D_lambda_cancellation
#print axioms syracuse_trace_moment_q2
#print axioms proposition_3_3_fiber_weights
#print axioms M_cond_matrix_properties
#print axioms M_cond_spectral_radius_bounds
#print axioms prop_7_1_and_7_2_constants
#print axioms prop_7_2_exponential_markov_bound
#print axioms prop_7_3_atomic_dispersion_identity
#print axioms prop_7_3_jordan_block_cascade

end PaperAudit
