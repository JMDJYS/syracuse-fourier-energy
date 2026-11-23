# Syracuse Fourier Energy

**Convergence of Primitive Fourier Energy for the 3-adic Syracuse Random Model and Contraction of Affine Transfer Operators**

Research preprint dated November 23, 2026. Repository maintained by [JMDJYS](https://github.com/JMDJYS).

# 中文介绍

本仓库公开研究预印本的 LaTeX 源码及配套 Lean 4 形式化项目。

本研究考察由独立同分布的几何随机变量驱动的 **3-adic Syracuse 随机模型**。

设 \(a_1,a_2,\ldots\) 为独立同分布的几何随机变量，满足

$$
\mathbb P(a_i=a)=2^{-a},\qquad a\geq 1.
$$

定义随机变量

$$
Z_0=0,\qquad
Z_m\equiv 2^{-a_m}(1+3Z_{m-1})
\pmod{3^m},
$$

其中 \(2^{-a_m}\) 按模 \(3^m\) 的乘法逆元理解。

令其 Fourier 特征函数为

$$
\phi_m(\xi)=
\mathbb E\left[
\exp\left(\frac{2\pi i\xi Z_m}{3^m}\right)
\right].
$$

定义总 Fourier 能量与原初 Fourier 能量：

$$
E_m=
\sum_{\substack{\xi\in\mathbb Z/3^m\mathbb Z\\
\xi\neq 0}}
|\phi_m(\xi)|^2,
$$

$$
E_m^{\mathrm{prim}}=
\sum_{\substack{\xi\in\mathbb Z/3^m\mathbb Z\\
3\nmid\xi}}
|\phi_m(\xi)|^2.
$$

预印本的主要研究结论是：原初 Fourier 能量一致有界，并收敛到一个有限正数 \(I\)，进而得到总 Fourier 能量的线性渐近关系：

$$
E_m^{\mathrm{prim}}=O(1),
\qquad
E_m^{\mathrm{prim}}\longrightarrow I\in(0,\infty),
$$

$$
E_m=Im+o(m).
$$

其中，

$$
E_m=E_{m-1}+E_m^{\mathrm{prim}},
$$

而 \(I\) 是本文定义的渐近碰撞能量常数。

除上述能量渐近问题外，本文还研究原初 Mackey 壳的张量分解、仿射转移算子的谱隙、条件收缩性质以及 Følner 障碍。

**研究范围说明：** 以上结果针对所定义的 Syracuse 随机模型，不构成对确定性 Collatz 猜想的完整证明。本仓库发布的是公开研究预印本及其 Lean 4 形式化项目，不代表研究成果已经通过期刊同行评审。

---

# English Overview

This repository provides the LaTeX source code of a research preprint together with its accompanying Lean 4 formalization project.

The research investigates a **3-adic random Syracuse model** driven by independent and identically distributed geometric random variables.

Let \(a_1,a_2,\ldots\) be i.i.d. geometric random variables satisfying

$$
\mathbb P(a_i=a)=2^{-a},\qquad a\geq 1.
$$

Define the random variables

$$
Z_0=0,\qquad
Z_m\equiv 2^{-a_m}(1+3Z_{m-1})
\pmod{3^m},
$$

where \(2^{-a_m}\) is interpreted as the multiplicative inverse modulo \(3^m\).

Define the associated Fourier characteristic function by

$$
\phi_m(\xi)=
\mathbb E\left[
\exp\left(\frac{2\pi i\xi Z_m}{3^m}\right)
\right].
$$

We introduce the total Fourier energy and the primitive Fourier energy:

$$
E_m=
\sum_{\substack{\xi\in\mathbb Z/3^m\mathbb Z\\
\xi\neq 0}}
|\phi_m(\xi)|^2,
$$

$$
E_m^{\mathrm{prim}}=
\sum_{\substack{\xi\in\mathbb Z/3^m\mathbb Z\\
3\nmid\xi}}
|\phi_m(\xi)|^2.
$$

The main claimed results of the preprint concern the uniform boundedness and convergence of the primitive Fourier energy to a finite positive constant \(I\), yielding the following linear asymptotic law for the total energy:

$$
E_m^{\mathrm{prim}}=O(1),
\qquad
E_m^{\mathrm{prim}}\longrightarrow I\in(0,\infty),
$$

$$
E_m=Im+o(m).
$$

Here,

$$
E_m=E_{m-1}+E_m^{\mathrm{prim}},
$$

and \(I\) denotes the asymptotic collision-energy constant defined within this model.

Beyond these energy asymptotics, the manuscript investigates tensor factorization of the primitive Mackey shell, spectral gaps for affine transfer operators, conditional contraction properties, and Følner-type obstructions.

**Scope and disclaimer:** These results concern the specified random Syracuse model and do not constitute a complete proof of the deterministic Collatz conjecture. This repository contains a publicly available research preprint and its accompanying Lean 4 formalization project. The work has not necessarily undergone peer review by a scientific journal.

## Manuscript

- [LaTeX source](paper/main.tex)
- [Formal verification scope / Lean 验证范围](FORMAL_VERIFICATION.md)

The manuscript states a primitive-energy convergence theorem for the stationary 3-adic Syracuse offset law, using a linear total-energy estimate attributed to Weaver and a residue-class overlap argument. It also develops affine transfer-operator factorizations and contraction estimates. These are the manuscript's claims; repository publication does not constitute an independent mathematical audit.

## Lean 4 verification

The author checked the companion project with **Lean 4.24.0 and Mathlib v4.24.0**. The supplied log records 34 axiom checks, each listing only `propext`, `Classical.choice`, and `Quot.sound`.

- [Lean project and reproduction commands](lean/README.md)
- [Abstract measure-theoretic closure](lean/SyracuseEnergy.lean)
- [Algebraic and spectral checks](lean/PaperAudit.lean)
- [Author's verification log](lean/lean-check.log)

The paper provides the proof that connects the concrete Syracuse model to the abstract Lean hypotheses. For the correspondence between the paper and code, see [the formal verification scope](FORMAL_VERIFICATION.md).

## Build the paper

With a LaTeX installation containing the packages used by the manuscript:

```sh
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper/main.tex
```

The output is `build/main.pdf`. If using pdfLaTeX directly, run it at least twice to resolve cross-references. The PDF build can also be run in GitHub Actions.

## Attribution and reuse

The supplied manuscript text is preserved. No reuse license is specified for this initial preprint.
