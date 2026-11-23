# Syracuse Fourier Energy

**Convergence of Primitive Fourier Energy for the 3-adic Syracuse Random Model and Contraction of Affine Transfer Operators**

Research preprint dated November 23, 2026. Repository maintained by [JMDJYS](https://github.com/JMDJYS).

## 中文介绍

本仓库公开研究预印本的 LaTeX 源码和配套 Lean 4 形式化项目。研究对象为几何随机变量驱动的 3-adic Syracuse 随机模型：

$$
\mathbb P(a_i=a)=2^{-a}\quad(a\ge1),\qquad
Z_0=0,\quad Z_m\equiv2^{-a_m}(1+3Z_{m-1})\pmod{3^m}.
$$

设 $\phi_m(\xi)=\mathbb E[\exp(2\pi i\xi Z_m/3^m)]$，定义

$$
E_m=\sum_{\substack{\xi\bmod 3^m\\\xi\ne0}}|\phi_m(\xi)|^2,
\qquad
E_m^{\mathrm{prim}}=\sum_{\substack{\xi\bmod3^m\\3\nmid\xi}}|\phi_m(\xi)|^2.
$$

文稿主张证明原初 Fourier 能量一致有界、收敛至有限正数 $\mathcal I$，并由此得到总能量的线性渐近：

$$
E_m^{\mathrm{prim}}=O(1),\qquad
E_m^{\mathrm{prim}}\longrightarrow\mathcal I\in(0,\infty),\qquad
E_m=\mathcal I m+o(m).
$$

其中 $E_m=E_{m-1}+E_m^{\mathrm{prim}}$；$\mathcal I$ 是本文定义的渐近碰撞能量常数。文稿还研究原初 Mackey 壳的张量分解、仿射转移算子的谱隙、条件收缩及 Følner 障碍。

**以上为随机模型的研究主张，不构成对确定性 Collatz 猜想的完整证明。本仓库发布属于公开预印本发布，不代表已通过期刊同行评审。**

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
