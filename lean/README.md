# Lean 4 Formal Verification: Primitive Fourier Energy and Affine Transfer Operators for the 3-adic Syracuse Model

This repository accompanies the manuscript:
> **Convergence of Primitive Fourier Energy for the $3$-adic Syracuse Random Model and Contraction of Affine Transfer Operators** ([manuscript source](../paper/main.tex))

The supplied verification log records checks with **Lean 4.24.0** and **Mathlib v4.24.0** under `-DwarningAsError=true`, with zero `sorryAx` and zero custom axioms.

---

## Scope Statement (Modular Formalization Architecture)

> **Important Scope Note**: The accompanying Lean 4 formalization (`SyracuseEnergy.lean` and `PaperAudit.lean`) verifies:
> 1. **The abstract measure-theoretic closure (`SyracuseEnergy.lean`)**: the Fatou–Vitali–conditional expectation pipeline yielding $E_m^{\mathrm{prim}} = O(1)$, $E_m^{\mathrm{prim}} \to \mathcal{I} \in (0, \infty)$, and the Cesàro limit $E_m / m \to \mathcal{I}$, as well as the measure-preserving preimage intersection bound and countable convex mixture Tonelli lower bound; and
> 2. **All key algebraic identities, parity-filtered congruence reductions, $3$-adic valuations, and spectral radius bounds (`PaperAudit.lean`)**: including the modulo-$3^{m+1}$ collision reductions, geometric collision weights, $v_3(4^{3^j}-1) = j+1$, the weak-$L^2$ level-set Markov step, the modulo-$pM$ Mackey phase tensor split, the $1$D Gram monomial collapse ($\sup_d \|B_d^{(0)}\|_{2\to 2}^2 \le 27/49 < 1$), the conditional Markov matrix $M_{\mathrm{cond}}$ and its Perron spectral radius enclosure $0.756898 < \vartheta < 0.756899 < 1$, and the $\mathcal{F}_{0,2}$ Jordan-block cascade.
>
> Connecting the concrete $3$-adic Syracuse random variable $Z_m \bmod 3^m$ and its Haar density $\rho \in L^1(\mathbb{Z}_3, m_3)$ to the four structural hypotheses (`hlinear`, `hidentity`, `hoverlap`, `hdom`) of `primitive_energy_from_collision_products` is presented in detail in **Section 2** (Table 1) of the paper.

---

## 中文说明（核验范围与定位）

本项目属于**“核心实分析/测度论收尾引擎 + 关键代数/同余/谱半径计算的模块化形式化核验（Modular Formalization）”**：

1. **`SyracuseEnergy.lean`（Theorem 1.1 & Lemma 2.3 测度论与收敛闭环）**：
   - `prefix_affine`：Local Density Lemma 中任意有限步前缀仿射复合的有理数展开。
   - `preimage_inter_overlap` / `high_set_product_lower_bound` / `convex_mixture_product_lower_bound`：高密度集合在两个保测度仿射变换下的重叠下界 $\eta = \delta^2(2\mu(G)-1)$，以及用 $\mathbb{R}_{\ge 0}^\infty$ 上的 Tonelli 定理将下界严格传递给任意两个可数凸混合。
   - `exists_late_shell_le` / `weighted_fatou_of_linear_energy`：**不预先假设极限乘积 $q_r = \rho(\rho\circ\Theta_r)$ 可积**，仅由非负壳层增量与线性部分和上界 $E_m \le C m$ 构造晚时刻低能量子列，结合 Fatou 引理导出 $q_r \in L^1$ 与 $\mathcal{I} \le C < \infty$。
   - `vitali_of_condExp_bound` / `primitive_energy_convergence` / `primitive_energy_from_collision_products` / `weighted_collision_errors_tendsto_zero`：由条件期望 $\mathbb{E}[\eta^{-1} q_r \mid \mathcal{F}_m]$ 控制给出一致可积性，接通 Vitali $L^1$ 收敛定理、级数控制收敛定理与 Cesàro 平均定理，闭合证明 $0 < \frac{2}{3}\eta \le \mathcal{I} \le C$、$\sup_m E_m^{\mathrm{prim}} \le \eta^{-1}\mathcal{I}$、$\lim_{m\to\infty} E_m^{\mathrm{prim}} = \mathcal{I}$ 与 $\lim_{m\to\infty} E_m / m = \mathcal{I}$。
2. **`PaperAudit.lean`（Section 2 桥梁同余/级数引理 + Section 3–7 算子谱计算核验）**：
   - **Section 2 桥梁代数与数论引理**：`total_energy_eq_sum_primitive`（能量裂项）、`weak_L2_level_set_bound`（弱 $L^2$ 水平集尾界）、`mod_three_parity_filter`（模 3 奇偶筛选 $2^a \equiv 2^b \pmod 3 \iff 2 \mid (a-b)$）、`diagonal_congruence_reduction` 与 `shifted_congruence_reduction`（模 $3^{m+1}$ 碰撞降模至 $3^m$）、`collision_shift_algebraic_identity`、`diagonal_collision_weight_sum` 与 `off_diagonal_collision_weight_sum`（对角权重 $1$ 与移位权重 $4^{-r}$）、`four_pow_three_pow_exact_div`（3-adic 阶归纳 $v_3(4^{3^j}-1) = j+1$）、`cylinder_rescaling_domination`（柱集条件期望缩放）。
   - **Section 3–7 算子与谱半径定理**：`compatibility_congruence_identity`（Lemma 3.1）、`mackey_phase_tensor_split`（Theorem 1.4 模 $pM$ 相位自动提升与张量分裂）、`syracuse_W1_class_sums`（$W_1[0]=8/7, W_1[1]=11/7, W_1[2]=2/7$ 及谱上界 $27/49$）、`lemma_3_2_slope_ratio_distribution`、`syracuse_gram_monomial_collapse`、`syracuse_c1D_lambda_cancellation`、`syracuse_trace_moment_q2`（$1609/1575$）、`proposition_3_3_fiber_weights`、`M_cond_matrix_properties`、`M_cond_spectral_radius_bounds`（$0.756898 < \vartheta < 0.756899 < 1$）、以及 `prop_7_1_and_7_2_constants`、`prop_7_2_exponential_markov_bound`、`prop_7_3_atomic_dispersion_identity`、`prop_7_3_jordan_block_cascade`。

---

## Verification Commands / 复核命令

To reuse the original Windows verification script, provide the local `.tooling` layout referenced by `check.ps1`:

```powershell
.\check.ps1
```

Or in a standard Elan + Lake environment:

```bash
lake update
lake exe cache get
lake env lean -DwarningAsError=true SyracuseEnergy.lean
lake env lean -DwarningAsError=true PaperAudit.lean
```

The output log `lean-check.log` records the `#print axioms` verification for 34 declarations across both files, confirming that every theorem depends solely on `[propext, Classical.choice, Quot.sound]`.
