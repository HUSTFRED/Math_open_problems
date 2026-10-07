# RS42 论文与固定实例证明资料

整理日期：2026-10-07（Asia/Shanghai）。本地私有仓库存档包；未创建远程仓库、上传或投稿。

## 文件入口

- `paper/en/arxiv_en.tex`、相邻 `arxiv_en.pdf`：最新版英文稿；英文稿用于后续提交。
- `paper/zh/arxiv_zh.tex`、相邻 `arxiv_zh.pdf`：对应中文阅读稿。
- `lean/`：12 个 Lean 源文件、依赖锁文件、工具链与原构建脚本。
- `graph/tree90_edges.json`：90 顶点、89 边的固定图证书。
- `verification/`：原始构建和公理记录，以及本次包装、论文编译检查。
- `audit/historical_reproduction/`：独立 Python 检查器和原运行记录，按原样保留。
- `PROOF_MAP.md`：最新版论文结构的代码导航。
- `provenance/`：本地文件来源映射及明确标记的旧版说明，不作为当前论文。
- `SHA256SUMS`：本包文件完整性清单；`scripts/verify_package.py` 为跨平台核对脚本。

两种语言的论文根文件均自包含，图形与参考文献内嵌，无外部图片、BibTeX 数据库或用户自定义样式依赖。源码保持与 `output/latex/RS42_arxiv/` 的当前文件逐字节一致。PDF 与源码的摘要及编译器见 `verification/paper_build/BUILD_REPORT.json`。

## 证明范围与记录日期

论文证明整数参数 `p >= 6` 的无限反例族。Lean 完整覆盖固定的 `p = 6`、90 顶点实例，不能称为整个无限族已形式化。最终入口是 `lean/FormalProof/Research003/RS42Counterexample90Final.lean`。

保留的两次完整 Lean 构建发生在 **2026-10-04**。本次整理核对了 12 个源码与冻结清单、两份成功构建记录之间的 SHA-256 一致性，没有重新运行 Lean，也没有把历史 Python 结果伪称为本次运行。完整性检查不代替数学验证。

## 复现

Lean 复现需要 Linux 环境、Python 3.10+、Git 和 Lean/elan，工具链固定为 `leanprover/lean4:v4.34.0`。mathlib 固定在 `56a9a88447f391672d7aeea117da03b6f7016b0d`，其余依赖见 `lean/lake-manifest.json`。标准依赖及缓存不放进这个包。

```sh
cd lean
lake exe cache get
python3 build.py
```

不要运行 `lake update` 改动锁文件。`build.py` 使用 Linux 的 `fcntl`、`/proc` 和 CPU 亲和性接口，不能在普通 Windows Python 下直接执行。每次运行在新目录重编全部 12 个模块；各模块有资源和时间限制。历史详细环境、命令及内存数据见 `verification/BUILD_REPORT.md`。

独立 Python 检查器同样需要 Linux；从包根目录运行下列命令（若刚执行过上面的 `cd lean`，先返回包根），并把新结果写到新位置以保留历史证据：

```sh
python3 audit/historical_reproduction/check_tree90.py > new_python_check.json
```

不要在历史目录运行 `record_run.py` 覆盖既有记录。

LaTeX 源码常规编译方式：英文用 pdfLaTeX，中文用 XeLaTeX，通常重复两次以解析交叉引用。当前交付 PDF 的实际生成引擎、版本和诊断以本包编译报告为准。

## 完整性与私有仓库

在包根目录以 Python 3.10+ 运行 `python scripts/verify_package.py`（或 Linux 下 `sha256sum -c SHA256SUMS`）。本包未添加开源许可，也没有配置 GitHub Actions 或自动发布流程。自行建立 **Private** 仓库后，可上传此目录的内容；压缩包只是方便本地传递。不要把编译缓存、账号凭据或整个研究工作目录一起上传。

原始历史日志内含当时机器路径，是记录内容，不是复现时必须采用的路径。`FINAL_AUDIT.md` 及 `provenance/original_README.md` 中的完整开发历史、旧交付收据、旧清单和阶段文件均指原研究目录；本最小包没有收录所有开发失败日志、旧稿和渲染资料。`compare_historical.py` 依赖包外的旧候选结果，仅作为历史脚本保留，不是本包复现入口；独立的 `check_tree90.py` 已带齐必需图输入。

旧版浏览器打印 PDF 未作为最新版论文收录。原始研究目录仍保留在本地；本次清理只针对已确认被替代的旧整合压缩包。
