# 当前论文与固定实例源码导航

对应 `paper/en/arxiv_en.tex` / `paper/zh/arxiv_zh.tex`，整理于 2026-10-07。本表只提供导航，不构成新的数学证明或新的 Lean 验收。

| 当前论文位置 | 源码或记录 | 范围 |
|---|---|---|
| 第 1 节：原猜想及反例陈述 | `lean/FormalProof/Research003/RS42Counterexample90Target.lean` | 形式化采用固定 90 点、beta=1 的无歧义偶数阶实例。 |
| 第 2.1 节：树与匹配对 | `RS42Counterexample90.lean`、`RS42Counterexample90Library.lean`、`RS42Counterexample90Tree.lean` | 实际图、固定边表、树性质、完美匹配与独立数 45。 |
| 第 2.2 节：匹配对上的状态 | `RS42Counterexample90.lean`、`RS42Counterexample90Counts.lean`、`RS42Counterexample90CountingTools.lean` | 固定实例的独立集与合法状态、带权计数对应。 |
| 第 2.3–2.4 节：系数比较与极限 | 论文中的参数化组合证明 | 不宣称无限参数族的删点估计已全部形式化。 |
| 第 3.1 节：90 点精确系数 | `RS42Counterexample90Factors.lean`、`RS42Counterexample90Polynomial.lean`、`RS42Counterexample90CountFailure.lean` | 固定实例通过核心状态与乘积多项式精确求系数，是完整替代证明路线。 |
| 第 3.2 节：形式化结论 | `RS42Counterexample90Final.lean`、`RS42Counterexample90CountsAudit.lean` | 最终无条件反例、存在定理、猜想否定与公理审计。 |
| 附录 A.1：独立计算 | `audit/historical_reproduction/check_tree90.py` 和相邻原记录 | 删除递推与图分支乘法；运行记录为历史证据。 |
| 附录 A.2：形式化记录 | `verification/build_01/`、`verification/build_02/`、`verification/FINAL_AXIOMS.txt` | 2026-10-04 两次完整构建；本次仅核对源码身份。 |

除第一行已给出的完整路径外，表中的 Lean 文件均位于 `lean/FormalProof/Research003/`。更细的逐定理说明保存在 `provenance/original_PROOF_MAP.md`；其中章节编号、机器路径和开发阶段叙述属于旧版，不能直接当作当前稿件的章节编号。
