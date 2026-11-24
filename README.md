# Convergence of Primitive Fourier Energy for the 3-adic Syracuse Random Model and Contraction of Affine Transfer Operators

### 三进 Syracuse 随机模型中原初 Fourier 能量的收敛性与仿射转移算子的谱收缩

[![Verify Lean proofs](https://github.com/JMDJYS/syracuse-fourier-energy/actions/workflows/verify-lean.yml/badge.svg)](https://github.com/JMDJYS/syracuse-fourier-energy/actions/workflows/verify-lean.yml)

**Preprint Date / 预印本日期:** November 23, 2026 · **Author / 维护者:** [JMDJYS](https://github.com/JMDJYS)

相关独立项目 / Related project · [Collatz 周期的 108 个局部极小值证书与 Lean 4 源码](collatz-cycle-certificate/)

---

## 一、 中文简介 (Chinese Overview)

本仓库开源研究论文《*Convergence of Primitive Fourier Energy for the 3-adic Syracuse Random Model and Contraction of Affine Transfer Operators*》的 **LaTeX 源码**（[`paper/main.tex`](paper/main.tex)）以及配套的 **Lean 4.24.0 + Mathlib v4.24.0 形式化验证项目**（[`lean/`](lean/)）。

### 1. 研究对象与核心主定理（Theorem 1.1）

设 $a_1, a_2, \dots$ 为独立同分布的几何随机变量，满足：

$$\mathbb{P}(a_i = a) = 2^{-a}, \qquad a \ge 1.$$

定义模 $3^m$ 的 Syracuse 随机加性偏移量 $Z_m \in \mathbb{Z}/3^m\mathbb{Z}$ ：

$$Z_0 = 0, \qquad Z_m \equiv 2^{-a_m}(1 + 3 Z_{m-1}) \pmod{3^m},$$

其中 $2^{-a_m}$ 表示 $2^{a_m}$ 在单位群 $(\mathbb{Z}/3^m\mathbb{Z})^\times$ 中的乘法逆元。记其特征函数为：

$$\phi_m(\xi) := \mathbb{E}\!\left[\exp\!\left(\frac{2\pi i \xi Z_m}{3^m}\right)\right] \qquad (\xi \in \mathbb{Z}/3^m\mathbb{Z}),$$

并定义**总非零 Fourier 能量** $E_m$ 与**原初 Fourier 能量** $E_m^{\mathrm{prim}}$ ：

$$E_m := \sum_{\substack{\xi \bmod 3^m \\ \xi \neq 0}} |\phi_m(\xi)|^2, \qquad E_m^{\mathrm{prim}} := \sum_{\substack{\xi \bmod 3^m \\ 3 \nmid \xi}} |\phi_m(\xi)|^2.$$

由边缘一致性可得 $E_m = E_{m-1} + E_m^{\mathrm{prim}}$ （其中 $E_0 = 0$ ）。本文的核心定理（**Theorem 1.1**）结合 Weaver 的线性总能量上界、奇偶筛选碰撞分解、三进柱集上的一致重叠不等式以及条件期望主控的 Vitali 收敛论证，证明了原初 Fourier 能量在所有 3-adic 精度下一致有界，且收敛到严格正的渐近碰撞常数 $\mathcal{I} \in (0, \infty)$ ，并由 Cesàro 平均给出总能量的线性渐近律：

$$E_m^{\mathrm{prim}} = O(1), \qquad \lim_{m \to \infty} E_m^{\mathrm{prim}} = \mathcal{I} \in (0, \infty), \qquad E_m = \mathcal{I} m + o(m),$$

其中

$$\mathcal{I} := 2\sum_{r=1}^\infty 4^{-r} \int_{\mathbb{Z}_3} \rho(x)\,\rho\!\left(4^r x + \frac{4^r - 1}{3}\right) dm_3(x)$$

为平稳 3-adic Syracuse Haar 密度 $\rho \in L^1(\mathbb{Z}_3, m_3)$ 的异支碰撞积分。

### 2. 有限 3-adic 仿射群上的转移算子谱收缩理论（Theorems 1.4–1.6）

围绕二维有限仿射群 $\mathcal{G}_{p^d} = (\mathbb{Z}/p^d\mathbb{Z})^\times \ltimes (\mathbb{Z}/p^d\mathbb{Z})$ 上的原初 Mackey 频率壳层 $v_p(u) = 0$ ，本文进一步建立了三条算子谱定理与结构障碍分析：

1. **原初 Mackey 张量分解与一致 $L^2$ 谱隙（Theorem 1.4）**：在双线性频率坐标 $(x_1, x_2) = (\alpha' u, u)$ 下，原初壳层块算子精确分解为 $B_d^{(0)} \cong p^{-1/2}\overline{A_d} \otimes A_d$ 。对 $p=3$ Syracuse 半群，一维 Gram 算子 $H_d = A_d A_d^*$ 坍缩为绝对可和的酉单项式级数，满足 $\frac{5}{7}I \le H_d \le \frac{9}{7}I$ ，从而导出关于尺度 $d \ge 1$ 一致的谱隙 $\sup_{d \ge 1} \Vert B_d^{(0)} \Vert_{2\to 2}^2 \le \frac{27}{49} < 1$ 及高阶迹矩界 $\mathfrak{R}_{2q, d} \le (27/49)^q$ 。
2. **淬火斜率条件截距收缩（Theorem 1.5）**：固定斜率比序列 $q_t = \lambda_2 / \lambda_1$ 后，利用模 $p$ 相容类正交分解将任意斜率实现下的算子乘积归约为 $(p-1)\times(p-1)$ 加权 Markov 矩阵 $M_{\mathrm{cond}}$ 。在 $p=3$ 下求得 Perron 谱半径 $\vartheta = \rho(M_{\mathrm{cond}}) = \frac{425 + 4\sqrt{5266}}{945} \approx 0.756898 < 1$ ，给出一致指数收缩。
3. **顺从群 Følner 波包障碍与桥接障碍命题（Theorem 1.6 & Section 7）**：证明按单一相容类切片的算子范数满足 $`\lim_{d\to\infty} \Vert \widetilde{\mathcal{K}}_{\alpha, q, \kappa}^{(3^d)} \Vert_{2\to 2} = 1`$ ，并定量刻画了未切片路径 Cauchy–Schwarz 的 $9^L$ 发散损失、同胞陪集（sibling-coset）交叉项不可丢弃的初等指数矩下界，以及不动点陷阱族 $\mathcal{F}_{0,2}$ 产生的 $2\times 2$ Jordan 块共振级联。

### 3. Lean 4 形式化验证范围与研究边界声明

* **模块化形式化核验范围**：配套的 Lean 4 项目（[`lean/SyracuseEnergy.lean`](lean/SyracuseEnergy.lean) 与 [`lean/PaperAudit.lean`](lean/PaperAudit.lean)，在 `-DwarningAsError=true` 及 GitHub Actions CI 下自动通过，共 34 条形式化定理，零 `sorryAx`）严格核验了：(i) 抽象测度论收敛闭环（从柱集碰撞假设导出极限可积性的子列 Fatou 引理、条件期望控制的 Vitali $L^1$ 收敛定理、一致上界 $E_m^{\mathrm{prim}} \le \eta^{-1}\mathcal{I}$ 、极限 $E_m^{\mathrm{prim}} \to \mathcal{I}$ 与 Cesàro 极限 $E_m/m \to \mathcal{I}$ ）；以及 (ii) 全部关键代数恒等式、模 $3^{m+1}$ 奇偶筛选同余约化、几何级数权重、3-adic 阶归纳 $v_3(4^{3^j}-1) = j+1$ 、模 $pM$ Mackey 相位分裂、谱隙 $27/49$ 、条件 Markov 矩阵谱半径 $\vartheta \in (0.756898, 0.756899)$ 及 Jordan 块系数。将具体 3-adic Syracuse 模型连接到抽象定理四项假设（`hlinear`, `hidentity`, `hoverlap`, `hdom`）的完整推导由论文第 2 节（Table 1）给出；详见 [`FORMAL_VERIFICATION.md`](FORMAL_VERIFICATION.md)。
* **研究边界说明**： $E_m, E_m^{\mathrm{prim}}, \mathcal{I}$ 是本文针对 Syracuse 随机模型定义的特定 Fourier 能量泛函与渐近碰撞常数（并非某个既有 Erdős 猜想的标准记号）。上述能量渐近定理针对 Syracuse 随机偏移模型成立，**不构成对确定性 Collatz 猜想的完整证明**。

---

## 二、 English Overview

This repository hosts the LaTeX manuscript ([`paper/main.tex`](paper/main.tex)) and the companion **Lean 4.24.0 + Mathlib v4.24.0** formal verification project ([`lean/`](lean/)) for:

> **Convergence of Primitive Fourier Energy for the 3-adic Syracuse Random Model and Contraction of Affine Transfer Operators**

### 1. Problem Setup and Primary Result (Theorem 1.1)

Let $a_1, a_2, \dots$ be i.i.d. geometric random variables with $\mathbb{P}(a_i = a) = 2^{-a}$ ($a \ge 1$), and define the 3-adic Syracuse random additive offset modulo $3^m$ by

$$Z_0 = 0, \qquad Z_m \equiv 2^{-a_m}(1 + 3 Z_{m-1}) \pmod{3^m},$$

where $2^{-a_m}$ denotes the multiplicative inverse in $(\mathbb{Z}/3^m\mathbb{Z})^\times$. Writing $\phi_m(\xi) := \mathbb{E}[\exp(2\pi i \xi Z_m / 3^m)]$ ($\xi \in \mathbb{Z}/3^m\mathbb{Z}$), we study the **total Fourier energy** $E_m$ and the **primitive Fourier energy** $E_m^{\mathrm{prim}}$:

$$E_m := \sum_{\substack{\xi \bmod 3^m \\ \xi \neq 0}} |\phi_m(\xi)|^2, \qquad E_m^{\mathrm{prim}} := \sum_{\substack{\xi \bmod 3^m \\ 3 \nmid \xi}} |\phi_m(\xi)|^2 = E_m - E_{m-1}.$$

Combining Weaver's linear total-energy upper bound with a parity-filtered collision identity, a uniform residue-class overlap inequality on ternary cylinders, and a conditional-expectation dominated Vitali convergence argument, **Theorem 1.1** establishes that $E_m^{\mathrm{prim}}$ is uniformly bounded across all 3-adic depths and converges to a strictly positive distinct-branch collision integral $\mathcal{I} \in (0, \infty)$, yielding the linear asymptotic law for the total Fourier energy:

$$E_m^{\mathrm{prim}} = O(1), \qquad \lim_{m \to \infty} E_m^{\mathrm{prim}} = \mathcal{I} \in (0, \infty), \qquad E_m = \mathcal{I} m + o(m),$$

where

$$\mathcal{I} := 2\sum_{r=1}^\infty 4^{-r} \int_{\mathbb{Z}_3} \rho(x)\,\rho\!\left(4^r x + \frac{4^r - 1}{3}\right) dm_3(x)$$

for the stationary 3-adic Syracuse Haar density $\rho \in L^1(\mathbb{Z}_3, m_3)$.

### 2. Affine Transfer Operators on Primitive Mackey Shells (Theorems 1.4–1.6)

For 2D affine random walks on $\mathcal{G}_{p^d} = (\mathbb{Z}/p^d\mathbb{Z})^\times \ltimes (\mathbb{Z}/p^d\mathbb{Z})$ restricted to the primitive Mackey frequency shell $v_p(u) = 0$, the manuscript proves:

1. **Primitive Mackey tensor factorization and uniform $L^2$ spectral gap (Theorem 1.4)**: In the coordinate bijection $(x_1, x_2) = (\alpha' u, u)$, the primitive shell block factorizes as $B_d^{(0)} \cong p^{-1/2}\overline{A_d} \otimes A_d$. For the $p=3$ Syracuse semigroup, $H_d = A_d A_d^*$ collapses into an explicit 1D unitary monomial series satisfying $\frac{5}{7}I \le H_d \le \frac{9}{7}I$, $\sup_{d \ge 1} \Vert B_d^{(0)} \Vert_{2\to 2}^2 \le \frac{27}{49} < 1$, and $\mathfrak{R}_{2q, d} \le (27/49)^q$.
2. **Quenched-slope conditional intercept contraction (Theorem 1.5)**: Conditioning on the slope-ratio sequence $q_t = \lambda_2/\lambda_1$, modulo $p$ compatibility orthogonality reduces operator products to a $(p-1)\times(p-1)$ weighted Markov matrix $M_{\mathrm{cond}}$. For $p=3$, $\vartheta = \rho(M_{\mathrm{cond}}) = \frac{425 + 4\sqrt{5266}}{945} \approx 0.756898 < 1$.
3. **Amenable Følner barrier and structural bridge obstructions (Theorem 1.6 & Section 7)**: Slicing by a single compatibility class $\kappa \in \mathbb{Z}/3\mathbb{Z}$ forces $`\lim_{d\to\infty} \Vert \widetilde{\mathcal{K}}_{\alpha, q, \kappa}^{(3^d)} \Vert_{2\to 2} = 1`$, while Propositions 7.1–7.3 quantify the $9^L$ unsliced Cauchy–Schwarz loss, the necessity of sibling-coset cancellation, and the $\mathcal{F}_{0,2}$ Jordan-block trap cascade.

### 3. Scope of the Lean 4 Formal Verification & Repository Layout

* **Modular Formalization Scope**: The accompanying Lean 4 formalization ([`lean/SyracuseEnergy.lean`](lean/SyracuseEnergy.lean) and [`lean/PaperAudit.lean`](lean/PaperAudit.lean), checked in CI with Lean 4.24.0 and Mathlib v4.24.0 under `-DwarningAsError=true` across 34 declarations with zero `sorryAx`) verifies:
  1. the abstract measure-theoretic closure (the subsequence Fatou integrability step, the conditional-expectation dominated Vitali $L^1$ convergence step, and the Cesàro limit pipeline) yielding $E_m^{\mathrm{prim}} \to \mathcal{I}$ and $E_m / m \to \mathcal{I}$; and
  2. all key algebraic identities, parity-filtered modulo $3^{m+1}$ congruence reductions, geometric collision weights, 3-adic valuations ($v_3(4^{3^j}-1) = j+1$), modulo $pM$ Mackey phase tensor splitting, the $27/49$ spectral gap, the conditional Markov spectral radius enclosure $0.756898 < \vartheta < 0.756899 < 1$, and the $\mathcal{F}_{0,2}$ Jordan-block cascade.
  Connecting the concrete 3-adic Syracuse Fourier energy to the four abstract hypotheses (`hlinear`, `hidentity`, `hoverlap`, `hdom`) is presented in Section 2 (Table 1) of the paper; see [`FORMAL_VERIFICATION.md`](FORMAL_VERIFICATION.md) for the complete dictionary.
* **Disclaimer**: The functionals $E_m, E_m^{\mathrm{prim}}$ and constant $\mathcal{I}$ are defined specifically for the Syracuse random model studied here and do not resolve the deterministic Collatz conjecture.

| Path / 路径 | Description / 说明 |
| :--- | :--- |
| [`paper/main.tex`](paper/main.tex) | Full LaTeX manuscript / 论文 LaTeX 源码 |
| [`FORMAL_VERIFICATION.md`](FORMAL_VERIFICATION.md) | Formal verification scope & paper-to-Lean dictionary / 形式化核验范围与桥梁对照表 |
| [`lean/SyracuseEnergy.lean`](lean/SyracuseEnergy.lean) | Lean 4 measure-theoretic closure (`primitive_energy_from_collision_products`) |
| [`lean/PaperAudit.lean`](lean/PaperAudit.lean) | Lean 4 congruence bridge lemmas, 3-adic valuations, Mackey tensor split & spectral bounds |
| [`lean/lean-check.log`](lean/lean-check.log) | Recorded `#print axioms` log verified in GitHub Actions CI |
| [`.github/workflows/verify-lean.yml`](.github/workflows/verify-lean.yml) | Automated GitHub Actions CI workflow for Lean 4.24.0 + Mathlib v4.24.0 |

### Reproducing the Verification / 本地复现命令

```bash
# 1. Verify Lean 4 proofs (requires elan)
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true SyracuseEnergy.lean
lake env lean -DwarningAsError=true PaperAudit.lean

# 2. Build the LaTeX manuscript
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper/main.tex
```
