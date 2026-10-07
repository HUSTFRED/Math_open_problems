# 教师审阅：中文证明与 Lean 定理对应表

记录时间：2026-10-04 10:42 UTC。本文是一份阅读导航，不代替原论文、源码或实际构建日志。开发工作区的最终无条件90点反例定理已在`root_final_01`实际通过；随后教师包和第二份独立源码目录均在全新本地输出目录重建全部12个模块并成功。本表区分开发构建与两次完整源码复现。

## 1. 本轮 Lean 要证明的究竟是什么

中文论文给出参数 p≥6 的无限反例族。当前 Lean 只固定 p=6，构造一个**90 个顶点的真实有限简单树**，证明其独立数为45，并证明实际独立集数

\[
 a_{43}=4761097500672,\qquad
 a_{44}=5965496320,\qquad
 a_{45}=17567744,
\]

满足

\[
 a_{44}^{2}-a_{43}a_{45}=-48054595706911981568<0.
\]

一个经过完整验证的固定反例已足以否定全称猜想，不必先形式化整个无限族。但不得把“固定90点实例通过”写成“所有p≥6的无限族证明已经全部Lean化”。

原猜想代入 N=90、h=45、j=44、beta=1，若断裂则要求alpha≥47；实际alpha=45，矛盾。这里使用偶数阶和beta=1，不依赖原文对其他beta边界或奇数阶表述的任何额外解释。

正式最终存在命题是 `exists_counterexample90`：存在 `T : SimpleGraph (Fin 90)`，T是树，`T.indepNum=45`，其真正44元独立顶点集的基数平方严格小于43元与45元独立顶点集基数的乘积，且独立数不满足47下界。最终源码没有把树性质、系数值或断裂作为参数。

## 2. 论文步骤与源码对应

下列文件均位于 `FormalProof/Research003/`；所有短定理名在命名空间 `FormalProof.Research003.RS42Counterexample90` 内。

| 中文论文步骤 | Lean 文件与关键定义/定理 | 实际保证及范围 |
|---|---|---|
| §1 原猜想、量词与严格断裂 | `RS42Counterexample90Target.lean`：`RamosSun42Explicit`、`RamosSun42EvenBetaOne90`、`fixed_indices` | 使用真实独立集计数；明确N≥1、j≥1、j+beta=N/2；固定90点、beta=1的实例与原文无歧义对应。 |
| §2 从六点核心附加五组二点臂 | `RS42Counterexample90.lean`：`arrow45`、`splitGraph`、`blockGraph90`、`vertex90Equiv`、`graph90`、`fixedEdges90` | 45个匹配块，每块两个顶点；3个核心块和42个叶块。整数顶点编号为2i+b。 |
| §2 图确实是树 | `RS42Counterexample90Tree.lean`：`parentBlock90`、`rankBlock90`、`blockGraph90_adj_iff_parent`、`graph90_isTree` | 每个非根顶点有真实父边且秩严格下降；连通与边计数证明树性质，没有预设无圈。 |
| 图与交付边表是同一个对象 | 同文件：`fixedEdges90_eq_ranges`、`graph90_adj_iff_fixedEdges` | 89条literal边表的正反方向恰等于graph90邻接；计数没有换成另一幅图。 |
| §2 完美匹配与alpha=m | Base文件：`mate90_*`、`allPlus90_independent`、`allPlus90_card`、`graph90_independent_card_le`；`RS42Counterexample90Library.lean`：`matching90_isPerfectMatching`、`graph90_indepNum` | 每个匹配块至少给上界“独立集每块最多选一”；显式allPlus集合达到45。匹配与alpha均接mathlib真实图接口。 |
| §3–4 匹配块与状态的双向组合对应 | Base文件：`legal`、`selected`、`decode`、`decode_selected`、`selected_decode`、`independentCardStateEquiv`、`graph90_coefficient_eq_stateCount` | 每块状态是none、some0、some1，即空、+、−。原箭头i→k禁止同时选i的+和k的−；正反映射与大小条件都证明。 |
| §4 空块/已选块的大小计数 | `RS42Counterexample90Counts.lean`：`occupied`、`selected_card_eq_sum`、`selected_append_card` | 已选顶点数恰为非空块数。Lean采用三态权重而非先固定空块集合；两者承担同一组合接口。 |
| 将所有选择拆为核心与叶 | 同文件：`coreLeafStateEquiv90`、`no_leaf_leaf_arrow90`、`legal_append_iff`、`coreLeafCardEquiv90`、`coefficient_graph90_eq_coreLeaf_count` | 原45块的选择双向分成3块与42块。叶之间没有遗漏约束；核心/叶两个方向均检查。 |
| 以乘积记录条件独立叶选择 | `RS42Counterexample90CountingTools.lean`：`card_weighted_choices_eq_coeff`、`core_leaf_count_eq_coeff` | 对任意有限选择集合的一般恒等式：合法固定权重子类型的基数=局部权重多项式乘积的相应系数。其证明是有限分配律和系数提取，不是巨型状态枚举。 |
| §5–7 中用于90点实例的精确计数替代路线 | `RS42Counterexample90Factors.lean`：`leafAllowed90_iff`、`outgoing_sum`、`incoming_sum`、`five_group_product`、`corePolynomial90_closed` | 五组长度6、12、6、12、6给出线性因子的幂；只展开3个核心块的27种状态。**这里没有形式化论文的四个删点计数、叶扩张上界或全p阈值归纳，而是给固定p=6一条完整精确替代证明。** |
| 固定闭式的整数值与负差 | `RS42Counterexample90Polynomial.lean`：`independentPolynomial90_expansion`、`independentPolynomial90_coeff43/44/45`、`independentPolynomial90_strict_failure`、`independentPolynomial90_signed_difference` | 完整46项展开经普通ring证明；三个目标系数和整数负差经普通证明项检查。表中整数不是公理。 |
| 把多项式值接回真实图 | `RS42Counterexample90CountFailure.lean`：`graph90_coefficient_eq_polynomial`、`graph90_coefficient43/44/45`、`graph90_count_failure`、`graph90_mathlib_count_failure` | 先证明对所有k的真实计数等于闭式系数，再取43、44、45。最后一个定理直接使用mathlib `IsNIndepSet` 子类型的Nat.card。 |
| §8 代回原猜想 | `RS42Counterexample90Final.lean`：`graph90_counterexample`、`exists_counterexample90`、`not_RamosSun42EvenBetaOne90`、`not_RamosSun42Explicit` | 具体树、alpha=45和真实严格断裂合并；否定全称目标。是否已有完整内核验收，以最终成功日志和源码摘要为准。 |

## 3. 教师可按什么顺序检查

先读 Final 的结论和 Target 的定义，确认要否定的确实是原量词的合法实例。再读 Tree 的父映射与边表等价，核对图；读 Library 的最大独立集与完美匹配，核对alpha。

计数主线建议按 Base 的独立集/状态双射 → Counts 的3+42分解 → CountingTools 的一般乘积系数恒等式 → Factors 的五组叶与27个核心状态 → Polynomial 的精确整数 → CountFailure 的真实计数连接阅读。这里最重要的接口是“对象没有换掉”和“局部条件覆盖所有边”，而不是三个大整数本身。

闭式可以单独手核。A=1+2X，C=1+X，W=A^18+XA^12 C^6+XA^6 C^12，R=A^18+XA^6 C^12。核心z为空或选+时得到(A^6+XC^6)W²；核心z选−时禁止上游u、v选+，得到XA^6R²。因此总式为

\[
 (A^6+XC^6)W^2+XA^6R^2.
\]

该纸面核对只是帮助理解；正式真计数相等由Lean定理给出。`ring`、`norm_num`、`omega`等策略在此生成由Lean内核检查的证明项；没有使用`native_decide`、新增计数公理或枚举全部2^90个顶点子集/3^45个块状态。普通`decide`只用于明确的小型可判定事实，不承担巨型独立集计数。

## 4. “标准三公理”是什么意思

`#print axioms` 是依赖审计，不是SHA检查。当前通过模块输出的三项为：

| 项目 | 含义 | 不应误读为 |
|---|---|---|
| `propext` | 逻辑等价命题可作为相等命题使用，即命题外延性。 | 不允许凭空证明任意命题。 |
| `Classical.choice` | 对已证明存在的对象作经典选择，支持经典有限集合等非计算性定义。 | 不从外部服务读入系数，也不允许猜中一个数就当证明。 |
| `Quot.sound` | 等价关系中的等价元素在商类型中相等，是Lean商类型设施的标准原理。 | 不为本项目加入图论或计数假设。 |

这些是Lean/mathlib标准逻辑基础中的依赖，所以准确说法是“没有新增项目公理，公理输出仅含上述标准项”，而不是“完全不依赖任何公理”。还需信任Lean内核实现、使用的工具链和标准依赖；完整复现脚本会锁定版本并重建全部本地导入闭包，但不声称从零重编整个mathlib或证明编译器自身正确。

任何`sorryAx`、占位公理、循环输入或未经证明的系数假设都不属于上述许可。最终判断要同时看源码命题是否带假设、完整本地依赖闭包是否成功、公理输出是否符合要求；单看exit0或哈希相同不足以回答数学问题。

## 5. 当前状态与阅读边界

已实际读取的成功记录：CountingTools04、Polynomial02、Factors04、Failure01、Tree09；Tree09源SHA为 `0e38aa251a27cdd01c45c302578f60abf5e354f4a624d9796930667b9013d6a0`，其两个结构定理仅依赖标准三公理。Final已在`root_final_01`于10:35:49 UTC实际通过，源码SHA `829a8aebe587e27363a5dacb05d0d03fd26a8ee7a23fb7c6b8efb64455503dc3`；其九个`#print axioms`均只含标准三项。独立审读实际`#check`输出，最终树反例和存在命题没有未证参数。教师包于10:37:28—10:39:20 UTC完成首轮全新12模块重建；第二份独立源码目录于10:40:10—10:41:46 UTC完成第二轮全新12模块重建。两份成功记录分别为`teacher_package/lean/builds/20261004T103728_410239Z/BUILD_SUCCESS.json`与`reproduction_fresh_01/builds/20261004T104010_894338Z/BUILD_SUCCESS.json`（相对于研究审计目录，交付副本见verification记录）。已独立核对全部12个源码摘要、Final与CountsAudit的实际公理输出及搜索路径；全部本地模块输出位于各自新建目录，两份源码逐一相同，未借用旧本项目.olean。标准依赖缓存仍按前述锁定修订复用。

历史`infrastructure_smoke_01`只重建Base、Library、Target和最小入口，它用于检查构建基础设施，不能当最终反例验收。源码、输入边表和报告的SHA-256解决的是身份与传输完整性问题；它们不替代计数双射、树性质证明或内核构建。

本文仅对应固定90点反例。两个旧受限族的全域结论、论文无限族的所有不等式、发现优先权、人类同行评议与出版状态均不是本轮固定实例Lean结果自动证明的内容。
