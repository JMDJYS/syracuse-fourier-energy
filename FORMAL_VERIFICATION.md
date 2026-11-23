# Lean formalization scope

The author checked the companion project with Lean 4.24.0 and Mathlib v4.24.0. The [supplied log](lean/lean-check.log) records 34 named declarations. Every entry lists `propext`, `Classical.choice`, and `Quot.sound`. The project includes the [toolchain version](lean/lean-toolchain), [Lake configuration](lean/lakefile.toml), and [reproduction commands](lean/README.md).

| Component | Scope |
| --- | --- |
| [SyracuseEnergy.lean](lean/SyracuseEnergy.lean) | Abstract measure-theoretic closure, including Fatou integrability, conditional-expectation domination, convergence of the primitive energy, and the Cesàro limit |
| [PaperAudit.lean](lean/PaperAudit.lean) | Selected algebraic identities, parity-filtered congruences and weights, 3-adic valuations, and spectral calculations |
| [Concrete Syracuse model](paper/main.tex) | Section 2 of the manuscript supplies the written argument connecting the Syracuse offset law to the abstract hypotheses |

The abstract declaration `SyracuseEnergy.primitive_energy_from_collision_products` takes the hypotheses `hlinear`, `hidentity`, `hoverlap`, and `hdom`. Section 2 of the manuscript maps each hypothesis to the argument for the concrete model.

## 中文说明

Lean 项目形式化了抽象测度论推导，以及若干代数恒等式、同余、三进赋值和谱界计算。将具体 Syracuse 随机模型接到抽象定理所需的四项假设，由论文第 2 节论证。随项目发布的日志记录了 34 个声明的公理依赖。
