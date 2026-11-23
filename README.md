# Syracuse Fourier Energy

**Convergence of Primitive Fourier Energy for the 3-adic Syracuse Random Model and Contraction of Affine Transfer Operators**

Research preprint dated November 23, 2026. Repository maintained by [JMDJYS](https://github.com/JMDJYS).

## 中文介绍

本仓库公开研究预印本的 LaTeX 源码。研究对象为几何随机变量驱动的 3-adic Syracuse 随机模型：

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

The author reports successful checking under **Lean 4.24.0 and Mathlib v4.24.0**, with zero `sorry` in the reported formalization.

The manuscript names `SyracuseEnergy.lean` and `PaperAudit.lean`. The author supplied a Lean project archive separately. Its source and build have yet to be verified for this repository.

The stated formalization covers an **abstract measure-theoretic closure theorem** and selected algebraic, congruence, valuation, and spectral calculations. The manuscript connects the concrete Syracuse model to the abstract hypotheses in its written proof. See [FORMAL_VERIFICATION.md](FORMAL_VERIFICATION.md) for the exact distinction.

## Build the paper

With a LaTeX installation containing the packages used by the manuscript:

```sh
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper/main.tex
```

The output is `build/main.pdf`. If using pdfLaTeX directly, run it at least twice to resolve cross-references. The PDF build can also be run in GitHub Actions.

## Attribution and reuse

The supplied manuscript text is preserved. No reuse license is specified for this initial preprint.
