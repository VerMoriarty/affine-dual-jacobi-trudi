# 仿射对偶 Jacobi–Trudi 恒等式：Lean 4 形式化

本仓库提供论文 *Affine Dual Jacobi–Trudi Identities for Classical Hall–Littlewood Polynomials via Complementary Minors* 的 Lean 4 形式化与复现材料。论文作者为 **Helen W. J. Zhang、Chengdong Zhao**；形式化开发者为 **Hangzhou Logicon AI Studio**。

[英文主说明](../README.md) · [完整复现说明与命题对应表](REPRODUCIBILITY.md) · [引用信息](../CITATION.cff)

当前正在准备公开发布。冻结版本为 `fidelity-20261031`，软件版本为 `0.2.0-rc3`。已有验收记录对应冻结工程，不能据此声称本仓库的 GitHub CI 已通过。

## 数学范围

形式化覆盖论文全部 **16 个编号命题环境**：Theorem A、B；Lemma 2.1；Proposition 2.2；Theorem 3.1；Lemma 3.2、3.3；Proposition 4.1、4.2、5.1；Lemma 5.2；Proposition 5.3；Lemma 5.4；Proposition 5.5、6.1；Corollary 6.2。第 17 个聚合证书另行覆盖 Corollary 6.2 末句的七种零参数特化；17 不是论文编号结果或 Lean 声明的数量。

七种情形为 `B0`、`Bminus`、`Bplus`、`C0`、`Ct`、`BC`、`Bt`。主要恒等式保留 `n ≥ 1`；`Bplus`、`Bt` 的行列式公式要求 `k ≥ 1`，宽度为零时另列归一化值 `1`；其余五式允许 `k = 0`。`Ct` 保留偶子格求和，`Bplus`、`Bt` 保留 `1/2` 因子。论文接口采用有理函数域，平方根情形用 `t = τ²`；一般域中的辅助商式不能直接用于任意奇点。零参数证书要求 `n, k ≥ 1`。

## 浏览与复验

[`formalization/`](../formalization/) 是冻结源 ZIP 的同字节可浏览投影，省略 `fidelity/runs/`、`fidelity/packets/`、`fidelity/reviews/` 和 `DELIVERY_MANIFEST.sha256`。完整工程与证据保存在 [`artifacts/`](../artifacts/) 的两个冻结 ZIP 中，由 [`source-view-manifest.json`](source-view-manifest.json) 绑定。完整 checker 需要解包后的证据目录；请在下述工作目录运行。

先安装 Python 3.10 或以上版本、Git、Elan 及[冻结工程说明](../formalization/README.md)所需的构建工具。在仓库根目录执行：

```sh
python3 tools/verify.py --check-only
python3 tools/verify.py --prepare-only
cd build/verification/affine_dual_jt_complete
lean --version
lake --version
lake exe cache get
cd ../../..
python3 tools/verify.py
```

包装脚本不安装依赖。Elan 根据解包工程的配置选用 Lean `4.35.0-rc3`；mathlib 固定在 `c55e6e786f49471c72fbddbec5415808896aec1e`。恢复依赖需要联网及数 GB 磁盘空间。保留锁文件，不运行 `lake update` 或旧的 `scripts/build_rc3.sh`。

`--check-only` 仅检查字节一致性，不编译 Lean；`--prepare-only` 准备或复用解包工作目录；无参数时运行原始完整 checker。新报告位于 `build/verification/affine_dual_jt_complete/fidelity/runs/`，只有完整运行退出 `0` 才表示该次验收通过。仅执行 `lake build` 不覆盖单独编译的 `FidelityLean` 模块。

## 证据边界

独立规范 `FidelityLean/Spec.lean` 仅导入 Mathlib；对象桥接与证书证明其精确命题类型。数学声明的传递公理允许集合为 `propext`、`Classical.choice`、`Quot.sound`。内核验证形式命题的证明；自然语言含义和证明路线的对应另有代理审阅记录支持。哈希不能认证审阅者身份、实际理解或上下文隔离声明。环境导出工具的 `unsafe main` 单独留证，数学模块不得导入该工具。

历史运行 `acceptance-final-20261031` 与 `final-delivery-zip-20261031` 记录了原主机上的通过结果；其中新建工程的重构建共享已检查的固定依赖缓存。当前 CI 的结果以对应提交的实际工作流为准。

冻结论文已提供 [`source.tex`](../formalization/source.tex) 与 [`source.pdf`](../formalization/source.pdf)。`paper/main.tex`、`paper/paper.pdf` 的极简披露版将在获得公开仓库地址与固定形式化提交后加入；准备阶段的本地论文副本不等于已发布文件。

用户提供的署名声明原文如下：

> This Lean 4 formalization was developed by Hangzhou Logicon AI Studio, with AI assistance from OpenAI Codex (GPT-6.1 Sol), under human supervision and review.

论文引用使用 [`CITATION.cff`](../CITATION.cff) 的 `preferred-citation`；顶层作者对应软件材料。发布准备期间不填入尚不存在的公开 URL 或 DOI。
