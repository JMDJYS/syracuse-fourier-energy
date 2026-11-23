import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The primitive-energy argument

This file checks the sequence argument of Theorem 7.2 and a measure-theoretic
step of Lemma 7.1. The final theorem has explicit hypotheses for the analytic
estimates on the Syracuse law and for the collision identity.
-/

open Filter Topology Function Finset MeasureTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace SyracuseEnergy

/-- Composition of the affine branches in prefix order. -/
def prefixMap : List ℕ → ℚ → ℚ
  | [], x => x
  | a :: w, x => (1 + 3 * prefixMap w x) / (2 : ℚ)^a

/-- The affine coefficient of a prefix is a power of three times a dyadic unit. -/
theorem prefix_affine (w : List ℕ) (x : ℚ) :
    prefixMap w x = prefixMap w 0 + ((3 : ℚ)^w.length / (2 : ℚ)^w.sum) * x := by
  induction w with
  | nil => simp [prefixMap]
  | cons a w ih =>
    simp only [prefixMap, List.length_cons, List.sum_cons]
    rw [ih, pow_succ, pow_add]
    field_simp
    ring

/-- A high-density set has a uniform intersection with its measure-preserving images. -/
theorem preimage_inter_overlap {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {G : Set X} {g h : X → X}
    (hG : MeasurableSet G) (hg : MeasurePreserving g μ μ)
    (hh : MeasurePreserving h μ μ) :
    μ G + μ G ≤ 1 + μ ((g ⁻¹' G) ∩ (h ⁻¹' G)) := by
  have hgG : μ (g ⁻¹' G) = μ G := hg.measure_preimage hG.nullMeasurableSet
  have hhG : μ (h ⁻¹' G) = μ G := hh.measure_preimage hG.nullMeasurableSet
  have hUnion : μ ((g ⁻¹' G) ∪ (h ⁻¹' G)) ≤ 1 := by
    simpa using (measure_mono (Set.subset_univ ((g ⁻¹' G) ∪ (h ⁻¹' G))) :
      μ ((g ⁻¹' G) ∪ (h ⁻¹' G)) ≤ μ Set.univ)
  calc
    μ G + μ G = μ (g ⁻¹' G) + μ (h ⁻¹' G) :=
      congrArg₂ (· + ·) hgG.symm hhG.symm
    _ = μ ((g ⁻¹' G) ∪ (h ⁻¹' G)) + μ ((g ⁻¹' G) ∩ (h ⁻¹' G)) :=
      (measure_union_add_inter _ (hh.measurable hG)).symm
    _ ≤ 1 + μ ((g ⁻¹' G) ∩ (h ⁻¹' G)) := add_le_add_right hUnion _

/-- If the density is at least delta on the reference set, its affine images
have a product integral bounded below by the intersection bound. -/
theorem high_set_product_lower_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {G : Set X} {g h : X → X}
    {ρ : X → ℝ≥0∞} {δ : ℝ≥0∞}
    (hG : MeasurableSet G) (hg : MeasurePreserving g μ μ)
    (hh : MeasurePreserving h μ μ) (hρ : ∀ x ∈ G, δ ≤ ρ x) :
    δ * δ * (μ G + μ G - 1) ≤ ∫⁻ x, ρ (g x) * ρ (h x) ∂μ := by
  let A := (g ⁻¹' G) ∩ (h ⁻¹' G)
  have hA : MeasurableSet A := (hg.measurable hG).inter (hh.measurable hG)
  have hmass : μ G + μ G - 1 ≤ μ A :=
    tsub_le_iff_right.mpr (by simpa [A, add_comm] using preimage_inter_overlap hG hg hh)
  calc
    δ * δ * (μ G + μ G - 1) ≤ δ * δ * μ A := mul_le_mul_left' hmass _
    _ = ∫⁻ x, A.indicator (fun _ => δ * δ) x ∂μ := (lintegral_indicator_const hA _).symm
    _ ≤ ∫⁻ x, ρ (g x) * ρ (h x) ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        exact mul_le_mul' (hρ (g x) hx.1) (hρ (h x) hx.2)
      · simp [Set.indicator_of_notMem hx]

/-- Tonelli carries the same product lower bound over to countable convex mixtures. -/
theorem convex_mixture_product_lower_bound {X ι κ : Type*} [MeasurableSpace X]
    [Countable ι] [Countable κ] {μ : Measure X} {f : ι → X → ℝ≥0∞}
    {g : κ → X → ℝ≥0∞} {a : ι → ℝ≥0∞} {b : κ → ℝ≥0∞} {η : ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ j, Measurable (g j))
    (ha : (∑' i, a i) = 1) (hb : (∑' j, b j) = 1)
    (hoverlap : ∀ i j, η ≤ ∫⁻ x, f i x * g j x ∂μ) :
    η ≤ ∫⁻ x, (∑' i, a i * f i x) * (∑' j, b j * g j x) ∂μ := by
  have hpoint (x : X) :
      (∑' i, a i * f i x) * (∑' j, b j * g j x) =
        ∑' i, ∑' j, (a i * b j) * (f i x * g j x) := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro i
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro j
    ac_rfl
  have hm (i : ι) (j : κ) : Measurable (fun x => (a i * b j) * (f i x * g j x)) :=
    measurable_const.mul ((hf i).mul (hg j))
  simp_rw [hpoint]
  rw [lintegral_tsum (fun i => (Measurable.ennreal_tsum (hm i)).aemeasurable)]
  calc
    η = ∑' i, ∑' j, (a i * b j) * η := by
      simp_rw [mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ha, hb, one_mul]
    _ ≤ ∑' i, ∫⁻ x, ∑' j, (a i * b j) * (f i x * g j x) ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [lintegral_tsum (fun j => (hm i j).aemeasurable)]
      apply ENNReal.tsum_le_tsum
      intro j
      rw [lintegral_const_mul _ ((hf i).mul (hg j))]
      exact mul_le_mul_left' (hoverlap i j) _

/-- The Vitali step for products dominated by conditional expectations of an
integrable function. In the paper the dominating function is the limit product
divided by the overlap constant. -/
theorem vitali_of_condExp_bound {X : Type*} {m₀ : MeasurableSpace X}
    {μ : Measure X} [IsFiniteMeasure μ] (ℱ : Filtration ℕ m₀)
    {f : ℕ → X → ℝ} {v q : X → ℝ}
    (hv : Integrable v μ) (hq : Integrable q μ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖(μ[v|ℱ n]) x‖)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (q x))) :
    Tendsto (fun n => eLpNorm (f n - q) 1 μ) atTop (𝓝 0) := by
  have hmajor : UnifIntegrable (fun n => μ[v|ℱ n]) 1 μ :=
    hv.uniformIntegrable_condExp_filtration.2.1
  have hui : UnifIntegrable f 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hmajor hε
    refine ⟨δ, hδ, fun n s hs hμs => le_trans (eLpNorm_mono_ae ?_) (hsmall n s hs hμs)⟩
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simp [Set.indicator_of_notMem hxs]
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hf
    (memLp_one_iff_integrable.2 hq) hui hae


/-- Index zero denotes the shift with r = 1 in the paper. -/
noncomputable def collisionWeight (r : ℕ) : ℝ := 2 * (1 / 4 : ℝ)^(r + 1)

theorem collisionWeight_nonneg (r : ℕ) : 0 ≤ collisionWeight r := by
  unfold collisionWeight
  positivity

theorem collisionWeight_factor (r : ℕ) :
    collisionWeight r = (1 / 2 : ℝ) * (1 / 4 : ℝ)^r := by
  rw [collisionWeight, pow_succ]
  ring

theorem summable_collisionWeight : Summable collisionWeight := by
  have h : Summable (fun r : ℕ => (1 / 4 : ℝ)^r) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  change Summable (fun r => collisionWeight r)
  simp_rw [collisionWeight_factor]
  exact h.mul_left (1 / 2 : ℝ)

theorem tsum_collisionWeight : (∑' r, collisionWeight r) = 2 / 3 := by
  simp_rw [collisionWeight_factor]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])]
  norm_num

/-- The centered total energy is the sum of all primitive shells up to that depth. -/
def totalEnergy (shell : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ range m, shell j

/-- A nonnegative sequence with linear partial sums must return below C + ε
arbitrarily late. -/
theorem exists_late_shell_le {shell : ℕ → ℝ} {C ε : ℝ}
    (hnonneg : ∀ m, 0 ≤ shell m)
    (hlinear : ∀ m, totalEnergy shell m ≤ C * (m : ℝ))
    (hε : 0 < ε) (N : ℕ) :
    ∃ m ≥ N, shell m ≤ C + ε := by
  by_contra! h
  obtain ⟨k, hk⟩ := exists_nat_gt ((N : ℝ) * C / ε)
  have hlarge : (N : ℝ) * C < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hlower : (k : ℝ) * (C + ε) ≤ ∑ i ∈ range k, shell (N + i) := by
    calc
      (k : ℝ) * (C + ε) = ∑ _i ∈ range k, (C + ε) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (h (N + i) (Nat.le_add_right N i)).le)
  have hfirst : 0 ≤ ∑ i ∈ range N, shell i := Finset.sum_nonneg (fun i _ => hnonneg i)
  have htotal := hlinear (N + k)
  unfold totalEnergy at htotal
  rw [Finset.sum_range_add] at htotal
  push_cast at htotal
  nlinarith

/-- Fatou's step applied before assuming integrability of the limiting products.
The weights may be absorbed into the nonnegative functions F and G. -/
theorem weighted_fatou_of_linear_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : ℕ → ℕ → X → ℝ≥0∞} {G : ℕ → X → ℝ≥0∞}
    {shell : ℕ → ℝ} {C : ℝ}
    (hf : ∀ m r, Measurable (F m r)) (hg : ∀ r, Measurable (G r))
    (hae : ∀ r, ∀ᵐ x ∂μ, Tendsto (fun m => F m r x) atTop (𝓝 (G r x)))
    (hshell : ∀ m, 0 ≤ shell m)
    (hlinear : ∀ m, totalEnergy shell m ≤ C * (m : ℝ))
    (hrows : ∀ m, (∑' r, ∫⁻ x, F m r x ∂μ) ≤ ENNReal.ofReal (shell m)) :
    (∑' r, ∫⁻ x, G r x ∂μ) ≤ ENNReal.ofReal C := by
  have hε (k : ℕ) : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  choose n hn hsmall using fun k =>
    exists_late_shell_le hshell hlinear (hε k) k
  have hnlim : Tendsto n atTop atTop := tendsto_atTop.2 fun N =>
    eventually_atTop.2 ⟨N, fun k hNk => hNk.trans (hn k)⟩
  have hupper : Tendsto (fun k : ℕ => ENNReal.ofReal (C + 1 / ((k : ℝ) + 1)))
      atTop (𝓝 (ENNReal.ofReal C)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun R => ?_
  let partialSum (k : ℕ) (x : X) := ∑ r ∈ range R, F (n k) r x
  have hmeas (k : ℕ) : Measurable (partialSum k) :=
    Finset.measurable_sum _ (fun r _ => hf (n k) r)
  have hlim : ∀ᵐ x ∂μ, liminf (fun k => partialSum k x) atTop = ∑ r ∈ range R, G r x := by
    filter_upwards [ae_all_iff.2 hae] with x hx
    exact (tendsto_finset_sum _ (fun r _ => (hx r).comp hnlim)).liminf_eq
  have hcap (k : ℕ) :
      (∫⁻ x, partialSum k x ∂μ) ≤ ENNReal.ofReal (C + 1 / ((k : ℝ) + 1)) := by
    rw [show (∫⁻ x, partialSum k x ∂μ) = ∑ r ∈ range R, ∫⁻ x, F (n k) r x ∂μ
      from lintegral_finset_sum _ (fun r _ => hf (n k) r)]
    exact (ENNReal.sum_le_tsum _).trans
      ((hrows (n k)).trans (ENNReal.ofReal_le_ofReal (hsmall k)))
  calc
    (∑ r ∈ range R, ∫⁻ x, G r x ∂μ) =
        ∫⁻ x, ∑ r ∈ range R, G r x ∂μ := (lintegral_finset_sum _ (fun r _ => hg r)).symm
    _ = ∫⁻ x, liminf (fun k => partialSum k x) atTop ∂μ := (lintegral_congr_ae hlim).symm
    _ ≤ liminf (fun k => ∫⁻ x, partialSum k x ∂μ) atTop := lintegral_liminf_le hmeas
    _ ≤ ENNReal.ofReal C := by
      rw [← hupper.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hcap)


/-- A finite set of limit collisions is bounded by the linear slope, without
assuming that the infinite limit series already converges. -/
theorem finite_collision_limit_le
    {K : ℕ → ℕ → ℝ} {L shell : ℕ → ℝ} {C : ℝ}
    (hK : ∀ m r, 0 ≤ K m r)
    (hidentity : ∀ m, HasSum (fun r => collisionWeight r * K m r) (shell m))
    (hlinear : ∀ m, totalEnergy shell m ≤ C * (m : ℝ))
    (hconv : ∀ r, Tendsto (fun m => K m r) atTop (𝓝 (L r))) (R : ℕ) :
    ∑ r ∈ range R, collisionWeight r * L r ≤ C := by
  have hrowNonneg (m r : ℕ) : 0 ≤ collisionWeight r * K m r :=
    mul_nonneg (collisionWeight_nonneg r) (hK m r)
  have hshell (m : ℕ) : 0 ≤ shell m := by
    rw [← (hidentity m).tsum_eq]
    exact tsum_nonneg (hrowNonneg m)
  let U := ∑ r ∈ range R, collisionWeight r * L r
  change U ≤ C
  by_contra! hUC
  let ε := (U - C) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hU : C + ε < U := by dsimp [ε]; linarith
  have hp : Tendsto (fun m => ∑ r ∈ range R, collisionWeight r * K m r) atTop (𝓝 U) := by
    exact tendsto_finset_sum _ (fun r _ => tendsto_const_nhds.mul (hconv r))
  obtain ⟨N, hN⟩ := eventually_atTop.1 <|
    hp.eventually (Ioi_mem_nhds hU)
  obtain ⟨m, hmN, hm⟩ := exists_late_shell_le hshell hlinear hε N
  have hmPartial : (∑ r ∈ range R, collisionWeight r * K m r) ≤ shell m := by
    rw [← (hidentity m).tsum_eq]
    exact (hidentity m).summable.sum_le_tsum _ (fun r _ => hrowNonneg m r)
  exact (not_lt_of_ge (hmPartial.trans hm)) (hN m hmN)

/-- The numerical collision-sum closure in Theorem 7.2.
The inputs are the exact finite-shell identity, the linear total-energy bound,
the integrated residue comparison, and termwise convergence of the overlaps. -/
theorem primitive_energy_convergence
    {K : ℕ → ℕ → ℝ} {L shell : ℕ → ℝ} {C η : ℝ}
    (hη : 0 < η)
    (hK : ∀ m r, 0 ≤ K m r)
    (hL : ∀ r, η ≤ L r)
    (hidentity : ∀ m, HasSum (fun r => collisionWeight r * K m r) (shell m))
    (hlinear : ∀ m, totalEnergy shell m ≤ C * (m : ℝ))
    (hcomparison : ∀ m r, η * K m r ≤ L r)
    (hconv : ∀ r, Tendsto (fun m => K m r) atTop (𝓝 (L r))) :
    let I := ∑' r, collisionWeight r * L r
    Summable (fun r => collisionWeight r * L r) ∧ 0 < I ∧
      (2 / 3 : ℝ) * η ≤ I ∧ I ≤ C ∧
      (∀ m, shell m ≤ η⁻¹ * I) ∧
      Tendsto shell atTop (𝓝 I) ∧
      Tendsto (fun m => totalEnergy shell m / (m : ℝ)) atTop (𝓝 I) := by
  dsimp only
  let limitTerm : ℕ → ℝ := fun r => collisionWeight r * L r
  have hlimitNonneg (r : ℕ) : 0 ≤ limitTerm r :=
    mul_nonneg (collisionWeight_nonneg r) (hη.le.trans (hL r))
  have hpartial (R : ℕ) : ∑ r ∈ range R, limitTerm r ≤ C :=
    finite_collision_limit_le hK hidentity hlinear hconv R
  have hs : Summable limitTerm := summable_of_sum_range_le hlimitNonneg hpartial
  have hdom (m r : ℕ) : collisionWeight r * K m r ≤ η⁻¹ * limitTerm r := by
    have h : K m r ≤ η⁻¹ * L r := by
      rw [← div_eq_inv_mul, le_div_iff₀ hη]
      simpa [mul_comm] using hcomparison m r
    simpa [limitTerm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left h (collisionWeight_nonneg r))
  have hbound (m : ℕ) : shell m ≤ η⁻¹ * ∑' r, limitTerm r := by
    rw [← (hidentity m).tsum_eq, ← tsum_mul_left]
    exact (hidentity m).summable.tsum_le_tsum (hdom m) (hs.mul_left _)
  have hconv_shell : Tendsto shell atTop (𝓝 (∑' r, limitTerm r)) := by
    have hconv' := tendsto_tsum_of_dominated_convergence (hs.mul_left η⁻¹)
      (fun r => (tendsto_const_nhds.mul (hconv r) :
        Tendsto (fun m => collisionWeight r * K m r) atTop (𝓝 (limitTerm r))))
      (Eventually.of_forall fun m r => by
        rw [Real.norm_of_nonneg (mul_nonneg (collisionWeight_nonneg r) (hK m r))]
        exact hdom m r)
    simpa only [(funext fun m => (hidentity m).tsum_eq)] using hconv'
  have hposBound : (2 / 3 : ℝ) * η ≤ ∑' r, limitTerm r := by
    have h := (summable_collisionWeight.mul_right η).tsum_le_tsum
      (fun r => mul_le_mul_of_nonneg_left (hL r) (collisionWeight_nonneg r)) hs
    rwa [tsum_mul_right, tsum_collisionWeight] at h
  have hpositive : 0 < ∑' r, limitTerm r :=
    (mul_pos (by norm_num) hη).trans_le hposBound
  refine ⟨hs, hpositive, hposBound, hs.tsum_le_of_sum_range_le hpartial,
    hbound, hconv_shell, ?_⟩
  change Tendsto (fun m => totalEnergy shell m / (m : ℝ)) atTop (𝓝 (∑' r, limitTerm r))
  simpa [totalEnergy, div_eq_mul_inv, mul_comm] using hconv_shell.cesaro

/-- Measure-theoretic form of the energy theorem. The limiting products need
not be integrable in the hypotheses. Fatou makes them integrable, then the
conditional-expectation comparison gives both the uniform majorant and
Vitali convergence before the weighted sums are taken. -/
theorem primitive_energy_from_collision_products {X : Type*} {m₀ : MeasurableSpace X}
    {μ : Measure X} [IsFiniteMeasure μ] (ℱ : Filtration ℕ m₀)
    {f : ℕ → ℕ → X → ℝ} {g : ℕ → X → ℝ} {shell : ℕ → ℝ} {C η : ℝ}
    (hη : 0 < η)
    (hf : ∀ m r, Measurable (f m r)) (hg : ∀ r, Measurable (g r))
    (hfint : ∀ m r, Integrable (f m r) μ)
    (hf0 : ∀ m r x, 0 ≤ f m r x) (hg0 : ∀ r x, 0 ≤ g r x)
    (hae : ∀ r, ∀ᵐ x ∂μ, Tendsto (fun m => f m r x) atTop (𝓝 (g r x)))
    (hidentity : ∀ m, HasSum (fun r => collisionWeight r * ∫ x, f m r x ∂μ) (shell m))
    (hlinear : ∀ m, totalEnergy shell m ≤ C * (m : ℝ))
    (hoverlap : ∀ r, ENNReal.ofReal η ≤ ∫⁻ x, ENNReal.ofReal (g r x) ∂μ)
    (hdom : ∀ m r, ∀ᵐ x ∂μ, f m r x ≤ (μ[η⁻¹ • g r|ℱ m]) x) :
    let I := ∑' r, collisionWeight r * ∫ x, g r x ∂μ
    (∀ r, Integrable (g r) μ) ∧ 0 < I ∧ I ≤ C ∧
      (∀ m, shell m ≤ η⁻¹ * I) ∧
      Tendsto shell atTop (𝓝 I) ∧
      Tendsto (fun m => totalEnergy shell m / (m : ℝ)) atTop (𝓝 I) := by
  dsimp only
  have hwpos (r : ℕ) : 0 < collisionWeight r := by unfold collisionWeight; positivity
  have hnonneg (m r : ℕ) : 0 ≤ collisionWeight r * ∫ x, f m r x ∂μ :=
    mul_nonneg (hwpos r).le (integral_nonneg (hf0 m r))
  have hrows (m : ℕ) :
      (∑' r, ∫⁻ x, ENNReal.ofReal (collisionWeight r * f m r x) ∂μ)
        ≤ ENNReal.ofReal (shell m) := by
    have hfinite (r : ℕ) :
        (∫⁻ x, ENNReal.ofReal (collisionWeight r * f m r x) ∂μ) =
          ENNReal.ofReal (collisionWeight r * ∫ x, f m r x ∂μ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal ((hfint m r).const_mul (collisionWeight r))
        (Eventually.of_forall fun x => mul_nonneg (hwpos r).le (hf0 m r x))]
      rw [integral_const_mul]
    simp_rw [hfinite]
    rw [← ENNReal.ofReal_tsum_of_nonneg (hnonneg m) (hidentity m).summable, (hidentity m).tsum_eq]
  have hfat :
      (∑' r, ∫⁻ x, ENNReal.ofReal (collisionWeight r * g r x) ∂μ) ≤ ENNReal.ofReal C := by
    apply weighted_fatou_of_linear_energy
      (fun m r => (measurable_const.mul (hf m r)).ennreal_ofReal)
      (fun r => (measurable_const.mul (hg r)).ennreal_ofReal) _ _ hlinear hrows
    · intro r
      filter_upwards [hae r] with x hx
      exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hx)
    · intro m
      rw [← (hidentity m).tsum_eq]
      exact tsum_nonneg (hnonneg m)
  have hgint (r : ℕ) : Integrable (g r) μ := by
    refine ⟨(hg r).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (hg0 r))).2 ?_⟩
    have ht : (∫⁻ x, ENNReal.ofReal (collisionWeight r * g r x) ∂μ) < ∞ :=
      (ENNReal.le_tsum r).trans_lt (hfat.trans_lt ENNReal.ofReal_lt_top)
    simp_rw [ENNReal.ofReal_mul (hwpos r).le] at ht
    rw [lintegral_const_mul _ (hg r).ennreal_ofReal] at ht
    apply lt_top_iff_ne_top.2
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (hwpos r)).ne'] at ht
    exact (lt_irrefl ∞) ht
  have hg_lower (r : ℕ) : η ≤ ∫ x, g r x ∂μ := by
    apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (hg0 r))).1
    rw [ofReal_integral_eq_lintegral_ofReal (hgint r) (Eventually.of_forall (hg0 r))]
    exact hoverlap r
  have hcomparison (m r : ℕ) :
      η * (∫ x, f m r x ∂μ) ≤ ∫ x, g r x ∂μ := by
    have hp := integral_mono_ae (hfint m r) integrable_condExp (hdom m r)
    rw [integral_condExp (ℱ.le m)] at hp
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul] at hp
    exact (le_inv_mul_iff₀ hη).1 hp
  have hconv (r : ℕ) :
      Tendsto (fun m => ∫ x, f m r x ∂μ) atTop (𝓝 (∫ x, g r x ∂μ)) := by
    apply tendsto_integral_of_L1' _ (hgint r) (Eventually.of_forall fun m => hfint m r)
    apply vitali_of_condExp_bound ℱ ((hgint r).smul η⁻¹) (hgint r)
      (fun m => (hf m r).aestronglyMeasurable) _ (hae r)
    intro m
    filter_upwards [hdom m r] with x hx
    rw [Real.norm_of_nonneg (hf0 m r x), Real.norm_of_nonneg ((hf0 m r x).trans hx)]
    exact hx
  obtain ⟨_, hpositive, _, hfinite, hbound, hshell, htotal⟩ :=
    primitive_energy_convergence hη (fun m r => integral_nonneg (hf0 m r)) hg_lower
      hidentity hlinear hcomparison hconv
  exact ⟨hgint, hpositive, hfinite, hbound, hshell, htotal⟩


/-- Countable weighted convergence of the L1 errors once the per-shift
Vitali convergence and residue-comparison majorant have been established. -/
theorem weighted_collision_errors_tendsto_zero
    {error : ℕ → ℕ → ℝ} {L : ℕ → ℝ} {η : ℝ}
    (hs : Summable (fun r => collisionWeight r * L r))
    (hnonneg : ∀ m r, 0 ≤ error m r)
    (herror : ∀ m r, error m r ≤ (1 + η⁻¹) * L r)
    (hconv : ∀ r, Tendsto (fun m => error m r) atTop (𝓝 0)) :
    Tendsto (fun m => ∑' r, collisionWeight r * error m r) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (hs.mul_left (1 + η⁻¹))
    (fun r => show Tendsto (fun m => collisionWeight r * error m r) atTop (𝓝 0) by
      simpa only [mul_zero] using tendsto_const_nhds.mul (hconv r))
    (Eventually.of_forall fun m r => by
      rw [Real.norm_of_nonneg (mul_nonneg (collisionWeight_nonneg r) (hnonneg m r))]
      simpa [mul_left_comm] using
        mul_le_mul_of_nonneg_left (herror m r) (collisionWeight_nonneg r))
  simpa using h

#print axioms prefix_affine
#print axioms high_set_product_lower_bound
#print axioms convex_mixture_product_lower_bound
#print axioms vitali_of_condExp_bound
#print axioms exists_late_shell_le
#print axioms weighted_fatou_of_linear_energy
#print axioms primitive_energy_convergence
#print axioms primitive_energy_from_collision_products
#print axioms weighted_collision_errors_tendsto_zero

end SyracuseEnergy
