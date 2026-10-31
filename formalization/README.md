# Affine Dual Jacobi–Trudi — Lean 形式化

## 原文忠实性验收入口

本目录现包含原始 Lean 工程和新增的独立规范、桥接证书、多代理审查与复现检查。统一入口：

```bash
python3 scripts/check_fidelity.py
```

具体流程、证据范围和恢复方法见 [fidelity/README.md](fidelity/README.md)。权威数学文本及原始材料哈希保存在 `fidelity/baseline.json`；每次验收报告保存在 `fidelity/runs/`，只有完整运行退出 0 才代表本次整体通过。新增规范位于 `FidelityLean/`，命名空间为 `Fidelity.Spec`；它们由只读原文的代理独立建立。

以下为原始交付包说明，保留其命题对照及运行方法。其中原有的“人工核验”等表述是原包声明，不充当本次全自动审查的证据；`delivery_logs/` 也是历史日志。本次内核、语义与复现状态以新的运行报告分别判定。

## 原工程基线说明

论文基准为 `source.tex`；数学代码均位于 `AffineDualJT/`。
环境：Lean `4.35.0-rc3` / mathlib `v4.35.0-rc3`。

**当前源码扫描为 0 个 `sorry/admit`，完整构建和传递公理审计通过。**
论文符号域中的 16 个编号命题环境均有已验证的 Lean 对应；**命题陈述和总体证明思路均符合原论文**。形式化补充了参数多项式特化等步骤；一般域接口中的含分母表达式在奇点处不自动代表多项式延拓值。


## 论文命题与 Lean 对照
`MainIdentities` 和 `HallLittlewood*` 提供一般域接口；`PaperIdentities`、`PaperPropositions` 和 `PaperSpecializations` 在论文使用的符号域中自动证明所需的正则性条件。

表中的 `模块.声明` 表示文件位置，声明的完整 Lean 名称为 `AffineDualJT.声明名`。

| 论文命题 | `source.tex` 行号 | Lean 对应位置 | 陈述范围 |
|---|---|---|---|
| Theorem A，(1.3)–(1.8) 及 B⁺ 的 `k=0` 情况 | 120–145 | `PaperIdentities.paper_theorem_A_1_3` … `_1_8`、`paper_theorem_A_Bplus_width_zero` | `n≥1`；除 (1.5) 外五式允许 `k=0`；(1.5) 要求 `k≥1`，`k=0` 时的值另列为 1 |
| Theorem B，(1.9) 及 Bₜ 的 `k=0` 情况 | 154–161 | `paper_theorem_B_1_9`、`paper_theorem_B_Bt_width_zero` | (1.9) 要求 `n,k≥1`；`k=0` 时的值另列为 1 |
| Lemma 2.1，(2.3)–(2.5) | 260–297 | `FiniteWeyl.lemma_2_1_eq_2_3/eq_2_4/eq_2_5` | 三个交错式；Lean 另覆盖空维数和任意节点 |
| Proposition 2.2，七种有限比值及 `det V_H=1` | 370–430 | `paper_prop_2_2_C0/Ct/BC/B0/Bminus/Bplus/Bt`；`FiniteColumnMinors.prop_2_2_minor_V*` | `n,k≥1` |
| Theorem 3.1 | 432–477 | `ComplementaryMinors.theorem_3_1`、`theorem_3_1_cleared`、`normalized_transfer_3_1` | 任意域；原文的核关系与四个非零子式条件 |
| Lemma 3.2，三组核等式与互补子式 | 507–558 | `Kernels.lemma_3_2_PhiC_DC/PhiB_DB/PhiPlus_DPlus`、`CoefficientMinors.lemma_3_2_minor_*` | 对应 `ζ, ζ, 2ζ`；`DPlus` 尾块保留正宽条件 |
| Lemma 3.3，(3.5)–(3.7) | 559–619 | `Folding.lemma_3_3_eq_3_5/eq_3_6/eq_3_7` | 任意以整数为索引的域值序列；有限性由系数核支撑推出 |
| Proposition 4.1 | 620–676 | `paper_prop_4_1_C0/BC` | `n,k≥1` |
| Proposition 4.2 | 677–739 | `paper_prop_4_2_B0/Bminus` | `n,k≥1`；B₀ 指数以已证明整除的整数除法表达 |
| Proposition 5.1 | 740–813 | `paper_prop_5_1_Ct` | `n,k≥1`；保留偶子格求和 |
| Lemma 5.2 | 814–838 | `paper_lemma_5_2_quasiperiod/center/affine/fixed` | 四个准周期、反射及固定点结论；符号域入口自动证明参数非零 |
| Proposition 5.3 | 839–893 | `paper_prop_5_3_Bplus` | `n,k≥1`；保留 `1/2` |
| Lemma 5.4 | 894–919 | `paper_lemma_5_4_eq_5_3/eq_5_4/eq_5_5/fixed` | 三个相邻项等式及固定点结论；符号域入口自动证明参数非零 |
| Proposition 5.5 | 920–971 | `paper_prop_5_5_Bt` | `n,k≥1`；保留 `1/2` |
| Proposition 6.1 | 972–1030 | `paper_prop_6_1_C0/Ct/BC/B0/Bminus/Bplus/Bt` | `n≥1`；七种类型在 `k=0` 时的归一化值均为 1 |
| Corollary 6.2，(6.1)–(6.3) 及七种零参数特化 | 1031–1063 | `paper_cor_6_2_eq_6_1/eq_6_2a/eq_6_2b/eq_6_2b_ratio/eq_6_3`、`paper_cor_6_2_*_zero` | 显示等式与原文末句；`n,k≥1` |

## 验证结果

当前项目使用 Lean `4.35.0-rc3` 与 mathlib `v4.35.0-rc3`。

| 检查 | 当前结果 |
|---|---|
| `lake build` | 通过，9046 个 jobs，0 warning |
| `bash scripts/check_formalization.sh` | 通过；源码严格检查为 88 个模块、16005 行 Lean、0 个 proof/definition hole、0 个自定义公理词元、0 个 unsafe 词元；论文命题传递公理审计通过 |
| `bash scripts/check_foundation.sh` | 通过；`FoundationAudit.lean` 检查 494 个基础声明 |
| `lake env lean AffineDualJT/Audit.lean` | 通过；审计 187 个论文命题及交付入口 |
| `python3 scripts/proof_status.py --write --strict` | 通过；0 个占位证明、0 个自定义公理词元、0 个 unsafe 词元 |

传递公理依赖仅为 Lean/mathlib 的 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler` 或项目自设公理。机器可读源码扫描结果保存在 [STATIC_CHECK.json](STATIC_CHECK.json)。

运行 `bash scripts/deliver.sh` 后，会生成 [环境](delivery_logs/environment.log)、[构建](delivery_logs/build.log)、[基础公理审计](delivery_logs/foundation.log)和[论文命题审计](delivery_logs/formalization.log)日志，以及仅保存在本地的解压复验日志 `delivery_logs/verification.log`。静态扫描覆盖 `AffineDualJT/` 下的 Lean 文件；公理审计覆盖对应审计文件中列出的声明及其传递依赖。命题陈述与证明路线对原论文的忠实度已经过人工逐项核验。

## 交付内容
| 路径 | 用途与管理方式 |
|---|---|
| `AffineDualJT/`、`AffineDualJT.lean` | Lean 数学源码和库入口，必须交付 |
| `lean-toolchain` | 固定 Lean 为 `leanprover/lean4:v4.35.0-rc3`，必须交付 |
| `lakefile.toml`、`lake-manifest.json` | 项目配置与依赖提交锁定文件，必须交付并保留原样 |
| `lean-toolchain.rc3`、`lakefile.rc3.toml` | 旧环境初始化脚本使用的配置副本，随源码保留 |
| `scripts/` 中的 `.py`、`.sh` | 源码检查、公理审计和交付打包工具，必须交付 |
| `README.md` | 使用说明、命题对照和验证结果，必须交付 |
| `source.tex`、`source.pdf` | 论文基准源码与 PDF |
| `.gitignore` | 缓存、本地配置和输出目录的忽略规则，随源码交付 |
| `delivery_logs/` | 验收脚本生成的日志；ZIP 仅收录 `environment.log`、`build.log`、`foundation.log`、`formalization.log` |
| `dist/` | 生成的 ZIP 压缩文件和 SHA-256 校验文件，仅供发送，不再装入 ZIP |
| `.lake/`、`__pycache__/`、`*.pyc` | 本地依赖和缓存，不打包 |
| `.git/`、`.agents/`、`.codex/`、`.aws/`、编辑器配置 | 版本历史和本地工具配置，不打包 |

在项目根目录执行下面这条命令即可完成自动化验收和打包。接收方在安装环境和恢复依赖后也可使用同一命令复验。
```bash
bash scripts/deliver.sh
```
## 安装环境

以下命令在 **Bash** 中执行，以 Ubuntu / Debian 为例。Windows 可在 WSL2 的 Ubuntu 中执行；macOS 需安装相同的命令行工具，并按 [Elan 官方说明](https://github.com/leanprover/elan#installation)安装版本管理器。项目的审计和打包脚本依赖 Bash、Python 3.9 及以上版本和 ripgrep（命令名为 `rg`）。

### 1. 安装基础工具和 Elan

Ubuntu / Debian：

```bash
sudo apt update
sudo apt install -y git curl ca-certificates python3 ripgrep unzip build-essential
```

尚未安装 Elan 时，使用官方安装脚本；已经安装可跳过：

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

安装程序的默认设置可用于本项目。项目根目录的 `lean-toolchain` 会选择项目所需版本，无需修改系统默认 Lean。首次准备环境需要能访问 GitHub、Lean 发行文件和 mathlib 缓存服务。

### 2. 校验并解压交付包

将 ZIP 和同名的 `.zip.sha256` 文件放在同一目录。下面以默认文件名为例；使用其他名称时替换对应文件名：

```bash
sha256sum -c affine_dual_jt_complete-source.zip.sha256
unzip affine_dual_jt_complete-source.zip -d verification
cd verification/affine_dual_jt_complete
sha256sum -c DELIVERY_MANIFEST.sha256
```

ZIP 外部校验用于确认收到的压缩包与发送方提供的校验值一致；包内 `DELIVERY_MANIFEST.sha256` 列出每个交付文件的 SHA-256，用于检查解压后的文件完整性。二者都不代替 Lean 的证明检查。macOS 手工校验时可将 `sha256sum -c` 替换为 `shasum -a 256 -c`；运行 `scripts/deliver.sh` 仍需提供名为 `sha256sum` 的命令，可安装 GNU coreutils 并将其 `gnubin` 目录加入 `PATH`。请解压到新的目录，避免混入已有文件。

### 3. 安装固定工具链并恢复依赖

在解压后的项目根目录执行：

```bash
elan toolchain install leanprover/lean4:v4.35.0-rc3
lean --version
lake --version
lake exe cache get
```

`lean --version` 应显示 `4.35.0-rc3`；Lake 随该工具链提供。`lake exe cache get` 会按项目依赖配置准备依赖，并下载 mathlib 编译缓存；新建的 `.lake/` 属于正常输出。下载和解压需要预留数 GB 磁盘空间，具体占用取决于平台和缓存内容。

**验收时保留 `lake-manifest.json`，不要运行 `lake update`，也不要更改版本配置。** 锁定文件中的 mathlib 提交为 `c55e6e786f49471c72fbddbec5415808896aec1e`。`scripts/build_rc3.sh` 是旧的环境初始化工具，会覆盖配置并执行 `lake update`，不作为本次交付的复现入口。

### 4. 构建与复验

恢复依赖后，如只需构建并检查证明，执行：

```bash
bash scripts/check_formalization.sh
bash scripts/check_foundation.sh
```

这两个脚本会先构建项目，再分别运行论文命题和基础声明的公理审计。需要生成验收日志和交付包时，执行前述 `bash scripts/deliver.sh`；该命令还会在新目录中解压、恢复依赖并重新构建，因此也需要网络访问和额外磁盘空间。
