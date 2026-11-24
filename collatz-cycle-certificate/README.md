# Collatz 周期的 108 个局部极小值证书

配套预印本为 *Odd-Step Budgets for Collatz Excursions and An Exact Certificate for 108 Local Minima*。见 [论文 LaTeX 源码](paper/Collatz_Excursions_and_Cycle_Certificate.tex)。

论文第 4 节证明任一非平凡正整数 Collatz 周期至少有 **108 个局部极小值**。Lean 主定理 [`Cycle108.no_107_cycle_computed`](Cycle108Computed.lean#L37) 将两个外部结果作为参数：Bařina 对小于 $2^{71}$ 的正整数的收敛验证，以及论文所引用的 Rhin 显式对数下界。形式化覆盖周期证书部分。论文对固定奇数段数的奇步预算与高度估计见第 2 节。

## 证明结构

- **Arithmetic、LogBounds、Tail** 检查六组幺模数据、实数对数夹逼、奇步预算的有理数比较和大奇步数尾界。
- **RunBudget、Weights、GrowthProfiles、Profile** 推出低位回返的逐段预算，并从周期数据推出 108 的下界。
- **Dynamics、FromCycle** 将真实周期旋转到其最小元素，再把相继的局部极小值与论文使用的估计连接起来。
- **HeightChecks、GridMiddle、GridLarge 系列** 验证形如“前两段共至多 \(k+24\) 个奇步”的不等式。Lean 由此推出另一组高度上界，并精确核对这组上界满足论文的两个预算要求。

## 本地复核

[原构建与公理审计日志](lean-check.log)记录了默认入口的检查结果。发布前用现有已编译依赖重新检查了主入口，退出码为 0，公理列表与原日志一致，未出现 `sorryAx`。

原 PowerShell 脚本使用 Lean 4.24.0 和 Mathlib v4.24.0。运行前，将 Windows 工具链目录 `lean-4.24.0-windows` 和已准备好缓存的 `mathlib4-4.24.0` 放到本项目的同级目录 `syracuse-energy-lean/.tooling/` 下。脚本会按依赖顺序检查本项目的源码，并将生成文件放在 `.build/`。

```powershell
.\check.ps1 -Modules @('Arithmetic','LogBounds','Tail','Profile')
.\check.ps1 -Modules @('FromCycle')
.\check.ps1
```

默认入口 `Cycle108Computed` 用 `native_decide` 检查三个最大的两段奇步界，因此主定理的依赖审计包含 `Lean.ofReduceBool` 和 `Lean.trustCompiler`。其余 14 组用 `decide +kernel` 检查。纯内核求值的入口 `Cycle108` 使用相同的数学证明和外部参数，其最大三组仍待完成内核复跑。

`FromCycle.lean` 与两个总入口都包含 `#print axioms`。审计时以实际构建退出状态和输出为准。命令带 `-Rebuild` 会从源文件重跑目标及其本地依赖。

两段奇步检查器和基础轨道引理改编自 [Justin Alick 的 Lean 仓库](https://github.com/justinalick/collatz-m-cycles-101-lean/tree/d1895945)。对应源码采用 Apache-2.0，许可证在 `LICENSE-Alick`。
