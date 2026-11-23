# Lean formalization: scope and reproducibility

## Reported status

The author reports that the formalization has passed Lean checking. The manuscript specifies Lean 4.24.0 and Mathlib v4.24.0 and reports zero `sorry` axioms.

The author supplied a Lean project archive separately. Its source and build have yet to be verified for this repository. The build status remains **author-reported**.

## Scope stated in the manuscript

| Component | Reported coverage |
| --- | --- |
| `SyracuseEnergy.lean` | Abstract measure-theoretic closure, including Fatou integrability, conditional-expectation dominated Vitali convergence, primitive-energy convergence, and the Cesàro limit |
| `PaperAudit.lean` | Selected algebraic identities, parity-filtered congruences and weights, 3-adic valuation induction, and spectral calculations |
| Concrete Syracuse model → abstract hypotheses | Written argument in the manuscript, with a hypothesis-to-lemma dictionary; not described here as an end-to-end Lean verification |

The abstract theorem is named `primitive_energy_from_collision_products`. Its structural hypotheses are `hlinear`, `hidentity`, `hoverlap`, and `hdom`. An abstract implication checked by Lean establishes its conclusion under its encoded hypotheses; applying it to the concrete random model requires those hypotheses to be established for that model.

## Reproducibility materials to add

- The complete Lean project, including `SyracuseEnergy.lean` and `PaperAudit.lean`.
- `lean-toolchain`, `lakefile.lean` or `lakefile.toml`, and the dependency manifest.
- The exact checked commit and full `lake build` output.
- A map from paper theorem statements to Lean declarations and their hypotheses.
- Axiom reports for the main declarations, including any project-specific assumptions.

Zero `sorry` alone does not document the meanings of definitions, the theorem-to-paper correspondence, or any additional assumptions. 
## 中文说明

作者表示已通过 Lean 检验。本文稿中列出的验证范围为抽象测度论结论和若干代数、同余、赋值及谱计算；具体 Syracuse 模型与抽象定理假设的连接由正文论证。作者已另外提供 Lean 项目压缩包。仓库尚待补入源码并复现构建。
