# Corollary 6.2 零参数特化：独立规范补充

本次只补充第14页 Corollary 6.2 最后一句的七种特化类型出口。原来的四个显示等式接口、原命题、已冻结 `Spec.lean` 和 `paper_a.json/md` 均未修改。第15页证明首两句说明：t=0（平方根情形同时 τ=0）时，每个有限列化为 [k+r]，由此识别相应有限比值。

数学输入仅为原论文 PDF/文本提取件与本代理已冻结的独立规范。未读取实现、其他规范、reviews、README 或 canonical 文件。下表引用自己的 raw A IDs，交由上层对应 canonical 义务；不猜造其他 ID。

## 逐类接口

| case | 原文目标 | 独立 Lean Prop | raw A 原子 ID |
|---|---|---|---|
| C0 | (6.1) 左侧 | `ZeroSpecializationC0 n k` | `C6.2.specialization.C0`、`C6.2.columns.C0` |
| Ct | (6.1) 左侧 | `ZeroSpecializationCt n k` | `C6.2.specialization.Ct`、`C6.2.columns.Ct` |
| BC | (6.1) 左侧 | `ZeroSpecializationBC n k` | `C6.2.specialization.BC`、`C6.2.columns.BC` |
| B0 | (6.2) 左侧 | `ZeroSpecializationB0 n k` | `C6.2.specialization.B0`、`C6.2.columns.B0` |
| Bminus | (6.2) 左侧 | `ZeroSpecializationBminus n k` | `C6.2.specialization.Bminus`、`C6.2.columns.Bminus` |
| Bplus | (6.3) 左侧 | `ZeroSpecializationBplus n k` | `C6.2.specialization.Bplus`、`C6.2.columns.Bplus` |
| Bt | (6.2) 左侧 | `ZeroSpecializationBt n k` | `C6.2.specialization.Bt`、`C6.2.columns.Bt` |

所有接口的前提都是 n>0、k>0。统一定义 `ZeroSpecialization c n k` 直接比较原 Weyl-sum 对象 `P c k (symbolicX n) 0 0` 与 `classicalNumerator (caseFolding c) k (symbolicX n) / Delta (caseFolding c) (symbolicX n)`；`Corollary62ZeroSpecializations` 对可枚举的七个 `PaperCase` 全称量化。

`Bplus` 标签保留固定边界参数 1，所以它代表的零参数值是 Pᴮ(x;0,1)。目标是 (6.3) 左侧有限比值，不能把右侧显示行列式的 1/2 再乘到这个比值上。

这里只定义 `Prop`，没有证明论文结果、没有桥接实现、没有新增公理或 sorry。类型检查通过不意味着这七个命题已获证明。

## 输入与冻结哈希

- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/inputs/authoritative.pdf`：`b13eaa9ed2a2dc2919980a702965a2d138ee634b49d9a32125ddeaa67fece7ab`。
- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/inputs/authoritative.txt`：`0cd074228dab999ce8217978668d5284f99f7fc610805a6e05e25ff94bc24a2f`。
- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/FidelityLean/Spec.lean`：`bf7dd88c9eb9537256f8290844e882dbd968652769c7b642663b5ef043ba66d0`。
- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/specs/paper_a.json`：`d68b0e5bba18573eddded78055b2d65121cf8c9c739453e49a7ce09511bc080f`。

- 新 Lean 文件 SHA-256：`b923dda633d8dd631c150fa90826a0e5191f29fcd77bea815ac4256de889b61d`。
- JSON 补充 SHA-256：`c31a6f43be890fc0427967b0cf06d063f93b095cb735b145e62a2b3252763377`。

## 验证

固定 Lean 4.35.0-rc3（commit `470d5ce1400764999581fd26d5d72b00d990b0f4`）通过项目 `lake env lean` 完成类型检查，退出码 0，无诊断；生成 `.lake/build/lib/lean/FidelityLean/ZeroParameterSpec.olean`。已再次校验三个既有冻结文件的哈希，均未改变。

待完成的工作仍是这七个特化命题的数学证明与实现到独立规范的证书；本补充不承担这些证明。
