# 原文忠实性审查

本目录保存论文到 Lean 的对应证据。入口为：

```bash
python3 scripts/check_fidelity.py
```

该命令验证固定环境、源码、公理依赖、独立规范证书、审阅记录、精确实验及两个新目录中的重构建。只有全部必需证据通过且仍对应当前源码，退出码才为 0。`--static-only` 和 `--skip-build` 都不能给出整体验收通过。

## 文件与信任范围

- `baseline.json`、`inputs/`：原始 PDF、源码包、辅助 TeX 与配置哈希。权威数学文本是用户单独提供的 PDF。包内 PDF 的数学正文与其一致，末页 AI 使用声明不同。
- `specs/paper_a.json`、`paper_b.json`：两个新上下文代理仅从原文独立抽取的 411、341 条义务。源文件不随实现修改。
- `specs/canonical_math.json`：第三个代理回到原文裁定后冻结的 424 条数学义务。`canonical_claims.json` 只增加实际 Lean 声明绑定。
- `../FidelityLean/Spec.lean`：只导入 Mathlib 的独立数学定义和命题。规范的命名空间为 `Fidelity.Spec`。物理目录采用 `FidelityLean`，以避免 macOS 上 `Fidelity` 与本目录 `fidelity` 的大小写冲突。
- `../FidelityLean/*Bridge.lean`、`*Certificates.lean`、`DerivedChecks.lean`：对象等价、精确规范类型的证明，以及原证明步骤的补充证书。
- `reviews/`：实际代理身份、所读材料哈希、逐项判断和分歧。独立性指输入及上下文隔离；哈希不能认证某个自然人或模型身份。
- `issues/registry.json`：当前问题状态；历史发现报告保留，问题关闭必须给出可核验的证据。
- `runs/`：每次运行的命令、原始输出、环境导出、退出码和报告。旧运行的成功状态不能替代当前构建。

完整类型和依赖来自固定 Lean 编译环境；文本扫描只作补充。公理允许集合固定为 `propext`、`Classical.choice`、`Quot.sound`。运行环境导出工具中的 `unsafe main` 仅用于 Lean 的环境加载接口，它独立记录工具哈希，不进入数学声明，也不能被数学模块导入。

## 独立代理的调度

协调代理用新的上下文启动各角色，不能把自己的聊天历史或其他审阅者结论传给盲审角色。可生成只包含允许材料的输入包：

```bash
python3 scripts/fidelity/prepare_review.py --role lean_reverse --environment fidelity/runs/RUN/environment.json
python3 scripts/fidelity/prepare_review.py --role semantic_1 --environment fidelity/runs/RUN/environment.json
python3 scripts/fidelity/prepare_review.py --role semantic_2 --environment fidelity/runs/RUN/environment.json
python3 scripts/fidelity/prepare_review.py --role route --environment fidelity/runs/RUN/environment.json
```

`lean_reverse` 输入包排除原文、独立规范及它们的编译声明，只保留实际实现的类型、定义和依赖。两位对照审阅者分别给出结论；路线审阅者检查实际证明依赖。生成输入包不会调用模型或产生通过结论，实际调度由协调代理完成。

## 偏差修复与重新验收

发现偏差时先保存原文定位、实际类型、影响义务和反例，再在项目副本中最小修改。独立数学规范保持冻结；修改规范必须重新回源抽取和裁定。每次数学源码或其依赖变化，都使对应旧审阅和证书失效。检查器采用保守的完整源码哈希绑定，尚未实现的精细失效优化不能扩大通过范围。

论文疑点保持未决，另列勘误候选；不能通过修改验收对象来使现有实现通过。环境不完整、检查超时、输入过期或审查分歧未解决时，保留检查点并返回非零退出码。

## 辅助实验

`experiment_design.md` 说明独立 Weyl 求和与仿射求和的精确算术实现、支撑界和故意错误探针。数值一致性用于定位问题，不证明一般恒等式。

`semantic_mutations.py` 还用固定 Lean 编译三种完整但目标错误的证明：重定义对象、把目标加作假设、缩小参数范围；随后要求独立规范类型拒绝这些证明。这样检查体系本身也接受反向检验。

最终报告分别给出对象、命题、证明路线、内核和复现状态。代理对自然语言的语义判断与内核可验证的形式证书分别留证，不能相互替代。
