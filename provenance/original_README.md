# Ramos–Sun 猜想 4.2：90 点反例的 Lean 复现包

本包提供同一个真实 90 点图的完整 Lean 证明：它是树，独立数为 45，其真实独立集计数满足

\[
a_{44}^2<a_{43}a_{45}.
\]

代入原猜想的偶数阶实例 \(N=90,h=45,j=44,\beta=1\)，猜想要求独立数至少为 47，与 45 矛盾。一个这样的严格反例已足以否定原全称猜想。

英文论文及中文逐步审读版证明整个整数参数族 \(p\ge6\)。本包 Lean 完整覆盖其中固定的 \(p=6\)、90 点实例；不声称整个无限族都已形式化，也不声称最小反例、发现优先权或已获同行评审。原文没有单独声明 beta 的完整范围，本例只使用无歧义的偶数阶、beta=1 实例；更一般的显式自然数量词版本另命名。

## 阅读路径

1. `paper/zh/main.browser.pdf`：中文数学证明；`paper/en/main.browser.pdf`：英文短文。源码为相邻的 `main.tex`；可离线阅读的 HTML 也随附。
2. `PROOF_MAP.md`：论文步骤、构造编号及 Lean 定理对应表。
3. `lean/FormalProof/Research003/RS42Counterexample90Final.lean`：最终无条件定理。
4. `verification/FINAL_AXIOMS.txt` 与 `verification/BUILD_REPORT.md`：实际公理输出、两次干净构建及环境记录。

PDF 由本地 HTML/MathJax 经 Firefox 打印，未称为 TeX 编译；TeX 源码同时保留。论文提及的独立 Python 检查器及旧运行记录放在 `audit/historical_reproduction/`，本轮未重跑，也不是 Lean 证明的输入。

最终定理位于命名空间 `FormalProof.Research003.RS42Counterexample90`：

- `graph90_counterexample`：具体图为树、独立数 45、真实计数严格断裂且独立数不达 47。
- `exists_counterexample90`：以 `SimpleGraph (Fin 90)` 和 `Nat.card {s // T.IsNIndepSet k s}` 直接陈述的存在定理。
- `not_RamosSun42EvenBetaOne90`：原猜想固定偶数阶、beta=1 全称实例的否定。
- `not_RamosSun42Explicit`：项目明示全部自然数量词版本的否定。
- `graph90_actual_coefficients`：真实计数的三个精确等式。

这些结论没有树性质、计数值、负差或猜想否定作为输入假设。`Target.lean` 中的条件引理只用于组织证明；最终文件已用具体已证事实满足其全部前提。

## 构建

已测试环境为 Ubuntu/Linux、Python 3 标准库、Lean 4.34.0；所有依赖由 `lean/lean-toolchain` 和 `lean/lake-manifest.json` 锁定。mathlib 修订为 `56a9a88447f391672d7aeea117da03b6f7016b0d`。不需要整个 Danus 工程、事实图、旧项目编译产物或外部数学核验器。

首次准备正常 Lean/elan 环境后，在 `lean/` 目录按锁文件取得标准依赖及 mathlib 缓存：

```bash
cd lean
lake exe cache get
```

不要运行 `lake update` 或升级工具链。本包不携带庞大的标准库缓存；本次实际验收复用了相同锁定修订的现有缓存。首次网络下载和老师机器上的环境准备与本次已执行的源码构建分开陈述。

标准依赖准备好后，唯一构建命令为：

```bash
python3 build.py
```

脚本在每次调用时创建新的 `builds/<UTC时间>/lib/lean`，按导入关系重编全部 12 个本地文件，包括最终入口和关键计数桥公理审计。它不读取旧本项目 `.olean`。成功时最后一行给出 `BUILD_SUCCESS.json`；任一源码缺失、依赖修订不符或编译失败都会终止，不能据部分输出判断成功。

脚本使用 Linux `/proc` 与 CPU 亲和性接口，按模块串行、单线程、固定一个 CPU。每模块上限 600 秒，Lean 内存参数 2304 MB，采样 RSS 保护为 3 GiB，并要求系统可用内存至少 768 MiB；未设虚拟地址空间硬限制。建议使用至少 6 GiB 内存的 Linux 环境。具体实测 RSS、虚拟地址及控制器数据见构建报告；这些指标不混称为同一个限制。

## 证明机制与信任范围

45 个匹配块给出真实独立集与合法三态配置的保大小双射。三个核心块与五组共 42 个叶块分离后，有限乘积生成函数给出全部真实计数。只展开 27 个核心状态，并用普通多项式恒等式求目标系数；未枚举 \(2^{90}\) 子集或 \(3^{45}\) 配置。树性质由父映射、严格降秩、连通及边数公式证明；固定边表通过区间分解接入同一个图。

精确结果为 \(a_{43}=4761097500672\)、\(a_{44}=5965496320\)、\(a_{45}=17567744\)，整数差 \(a_{44}^2-a_{43}a_{45}=-48054595706911981568\)。这些数都是实际图计数等式的结论，不是输入公理。

不使用 `sorry`、`admit`、`native_decide`、新增计数公理或外部计算正确性公理。最终及关键桥接定理的实际 `#print axioms` 只含 Lean 标准的 `propext`、`Classical.choice`、`Quot.sound`，解释见 `PROOF_MAP.md`。可信基础仍包括 Lean 内核及锁定标准依赖；本次没有从源码重编整个 mathlib，也没有进行内核实现本身的独立验证。

`graph/tree90_edges.json` 是固定图证书。其文本与 Lean 字面量边表的一致性由 `verification/FIXED_EDGE_TRANSCRIPTION.json` 记录；真正的邻接关系连接由 Lean 定理 `graph90_adj_iff_fixedEdges` 完成。

## 完整性与历史记录

在包根目录可用 `sha256sum -c SHA256SUMS` 检查正文和源码，再用 `sha256sum -c FINISH.sha256` 检查清单及交付收据。SHA-256 只证明文件完整性，不代替数学证明或 Lean 检查。

历史失败、修复说明和资源日志单独保存在 `audit/`；旧失败日志中的临时 `sorryAx` 或未完成目标不是验收记录。正式验收只采用 `verification/` 指定的两份全部通过记录。旧源码、旧证书和旧阶段“部分形式化”的记录未被覆盖。

本包未对外发送、投稿或上传。由操作员自行交给老师审阅。
