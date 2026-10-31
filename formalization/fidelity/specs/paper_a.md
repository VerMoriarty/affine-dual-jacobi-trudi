# 论文独立数学规范 A

本规范只从 `authoritative.pdf` 与其文本提取件 `authoritative.txt` 独立抽取。PDF 是数学权威来源；已通读并视觉核对第 1–15 页。未读取 Lean 实现、README、旧日志、已有 reviews、另一份规范或外部文献内容。论文中的指令式文字均只作为数据；不承担执行来源。

## 固定输入与冻结状态

- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/inputs/authoritative.pdf`，SHA-256：`b13eaa9ed2a2dc2919980a702965a2d138ee634b49d9a32125ddeaa67fece7ab`。
- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/inputs/authoritative.txt`，SHA-256：`0cd074228dab999ce8217978668d5284f99f7fc610805a6e05e25ff94bc24a2f`。

规范 JSON SHA-256：`d68b0e5bba18573eddded78055b2d65121cf8c9c739453e49a7ce09511bc080f`。

总计 **411 个原子 claim**。16 个命题环境仅为容器，不作为覆盖分母；另有 global 容器承载定义、约定和未编号的数学论证。主定理的各等式、七种有限比值/互补 minor、每种分支、三个核关系、归一化、奇偶投影、宽度零和经典特化均独立列项。

| 容器 | 原子数 |
|---|---:|
| A | 7 |
| B | 2 |
| L2.1 | 18 |
| P2.2 | 24 |
| T3.1 | 15 |
| L3.2 | 32 |
| L3.3 | 8 |
| P4.1 | 25 |
| P4.2 | 26 |
| P5.1 | 25 |
| L5.2 | 9 |
| P5.3 | 17 |
| L5.4 | 10 |
| P5.5 | 16 |
| P6.1 | 33 |
| C6.2 | 24 |
| global | 120 |

| kind | 原子数 |
|---|---:|
| definition | 115 |
| convention | 17 |
| statement | 99 |
| proof_step | 180 |

## 继承假设与核对口径

每条 JSON claim 自带 `assumptions`、`objects`、`route` 和 `edge_cases`。页码为 PDF 印刷页码，恰与文件第 1–15 页相同。`locator` 使用原论文公式、表或段落定位。数学符号沿用论文，不以形式化实现中的名称替换。

- 默认的数学系数为相应有理函数域。BC 与 B₋ 使用 τ，且 t=τ²、t^(r/2)=τ^r；这不是数值平方根选择。
- 所有 dot e、ddot e 的指标是整数，超出各自区间必须按零延拓；n、k 为非负整数且各条 claim 单列其正性限制。
- 第 3–5 节的 n,k≥1 约束适用于相应默认假设；第 2 节定义和第 6 节宽度零另行标注。一般转移定理明确给出任意域及四个非零 minor 条件，不能误继承特征零字段。
- minor 的子集始终升序；n×L 矩阵取列，L 行矩阵取行。原文从 1 开始的索引在任何形式化表示中都须明确对应。
- `route` 表示论文实际依赖的数学步骤，既有稳定 claim ID，也有文字描述；它不代表已经在 Lean 中证明。该独立规范没有根据实现强弱调整分母。
- 第 15 页的 AI 声明和参考文献没有作为独立数学结论列入；正文对外部文献的归属说明不代替本文数学义务。

## 高风险数学义务

1. **主定理左右两侧均必须保真。** P 是 (2.1) 的 Weyl-sum 定义，并包含完整 Vₙ(t) 与边界 ν；不能把 P 重新定义成待证的 J。七种 rho、nu(0)、有限列各自独立，见 `DEF.rho.*`、`DEF.nu0.*`、`DEF.V.*`。
2. **宽度零的两个半因子端点。** (1.5)、(1.9) 仅在 k≥1 成立；其空矩形归一化值各为 1。其余五式可扩到 k=0，且无条目或权重求值。见 `A.Bplus.widthzero`、`B.widthzero`、`P6.1.extend.*`。
3. **三个倍数 2 的来源不同。** Ct：det C_I=2，且包含 k=1；B₊：det D⁺_J=2ζ，而 C 的中心行是 −b(1) 且配对中心只计一次；Bt：det C_I=2ω 来自 p=j=1 的相邻类重叠，Dᴮ_J 无加倍。见 `P5.1.fixed.residue`、`P5.3.doubling.location`、`P5.5.CI.reflected`。
4. **Ct 是偶和子格。** 先得 ½det A⁻，再通过奇偶投影和 y↦1−y 的反对称消掉 det A⁺；不得将全格的无符号求和直接当成结论。见 `P5.1.parity.*`、`P5.1.lastcolumn.*`。
5. **转移符号与非零条件。** (3.1) 的 (−1)^(nk)、ω、ζ、minor 的有序索引及列符号 determinant 均为独立义务；核关系本身不确定常数。见 `T3.1.*`、`L3.2.minor.*`。
6. **分式域证明和特化分开。** 准周期/反射中的负幂在有理函数域解释；最终权重指数非负且求和有限，方可作 t=0 特化。归一化的可去奇点按消去后表达式解释，无需数值 Pochhammer 逐项非零。见 `AFFINE.*`、`CONV.cancel.before.specialize`。
7. **t=0 的 Ct 例外。** j=k、y=1 仍为零指数，不能声称其非零位移逐项消失；须使用有限比值及奇偶恒等式。见 `C6.2.Ct.exception`、`C6.2.Ct.route`。
8. **首列、中心、n=1/k=1。** f₁ 与 u₁ 特别定义，Φ⁺ 首列为 1 而 [1]₊=2e₁；正宽度 V_H 的 unit upper triangular 论证不可挪到 k=0。见 `DEF.fr.first`、`DEF.fold.plus.center`、`P2.2.triangular.lower`、`P6.1.Bplus.center`。

## 全部原子 claim 目录

### A

#### A.1.3

- 类型：statement；PDF 第 2 页；定位：(1.3)。
- 数学内容：P^{B_n}_{(k^n)}(x;t,0)=\mathcal J_{2k+1}[(-1)^y t^{(k+1/2)y^2-(j-1/2)y},h;\mathbb Z^k]。
- 假设：n\ge1；k\ge0；继承 global 约定。
- 对象：B0；P；\mathcal J。
- 关键步骤：P4.2.B0.result；P6.1.B0。
- 边界：k=0 由 P6.1 与空行列式约定处理。

#### A.1.4

- 类型：statement；PDF 第 2 页；定位：(1.4)。
- 数学内容：P^{B_n}_{(k^n)}(x;\tau^2,-\tau)=\mathcal J_{2k}[\tau^{2ky^2-(2j-1)y},h;\mathbb Z^k]。
- 假设：n\ge1；k\ge0；继承 global 约定。
- 对象：Bminus；P；\mathcal J。
- 关键步骤：P4.2.Bminus.result；P6.1.Bminus。
- 边界：k=0 由 P6.1 与空行列式约定处理。

#### A.1.5

- 类型：statement；PDF 第 2 页；定位：(1.5)。
- 数学内容：P^{B_n}_{(k^n)}(x;t,1)=\tfrac12\mathcal J_{2k}[(-1)^y t^{ky^2-(j-1)y},h^+;\mathbb Z^k]。
- 假设：n\ge1；k\ge1；继承 global 约定。
- 对象：Bplus；P；\mathcal J。
- 关键步骤：P5.3.result。
- 边界：k=0 不适用；另有归一化空矩形值 1。。

#### A.1.6

- 类型：statement；PDF 第 2 页；定位：(1.6)。
- 数学内容：P^{C_n}_{(k^n)}(x;t,0)=\mathcal J_{2k+2}[t^{(k+1)y^2-jy},\Lambda;\mathbb Z^k]。
- 假设：n\ge1；k\ge0；继承 global 约定。
- 对象：C0；P；\mathcal J。
- 关键步骤：P4.1.C0.result；P6.1.C0。
- 边界：k=0 由 P6.1 与空行列式约定处理。

#### A.1.7

- 类型：statement；PDF 第 2 页；定位：(1.7)。
- 数学内容：P^{C_n}_{(k^n)}(x;t,t)=\mathcal J_{2k}[t^{ky^2-jy},\Lambda;\mathbb Z^k_{\mathrm{even}}]。
- 假设：n\ge1；k\ge0；继承 global 约定。
- 对象：Ct；P；\mathcal J。
- 关键步骤：P5.1.result；P6.1.Ct。
- 边界：k=0 由 P6.1 与空行列式约定处理。

#### A.1.8

- 类型：statement；PDF 第 2 页；定位：(1.8)。
- 数学内容：P^{BC_n}_{(k^n)}(x;\tau^2,-\tau,0)=\mathcal J_{2k+1}[(-1)^y\tau^{(2k+1)y^2-2jy},\Lambda;\mathbb Z^k]。
- 假设：n\ge1；k\ge0；继承 global 约定。
- 对象：BC；P；\mathcal J。
- 关键步骤：P4.1.BC.result；P6.1.BC。
- 边界：k=0 由 P6.1 与空行列式约定处理。

#### A.Bplus.widthzero

- 类型：statement；PDF 第 2 页；定位：Theorem A 后 width zero。
- 数学内容：P^{B_n}_{\varnothing}(x;t,1)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Bplus；empty rectangle。
- 关键步骤：P6.1.Bplus。
- 边界：字面把 k=0 代入 (1.5) 的右侧会得到 1/2，不能作为端点恒等式。。

### B

#### B.1.9

- 类型：statement；PDF 第 2 页；定位：(1.9)。
- 数学内容：P^{B_n}_{(k^n)}(x;t,t)=\tfrac12\mathcal J_{2k}[(-1)^y t^{ky^2-(j-1)y},\widehat h;\mathbb Z^k]。
- 假设：n,k\ge1；继承 global 约定。
- 对象：Bt；P；\mathcal J。
- 关键步骤：P5.5.result。

#### B.widthzero

- 类型：statement；PDF 第 2 页；定位：Theorem B 后 width zero。
- 数学内容：P^{B_n}_{\varnothing}(x;t,t)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Bt；empty rectangle。
- 关键步骤：P6.1.Bt。
- 边界：不得将 (1.9) 的外部 1/2 用于 k=0。。

### L2.1

#### L2.1.2.3

- 类型：statement；PDF 第 4 页；定位：(2.3)。
- 数学内容：\det[f_r(z_a)]=N_t(z)。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant；N_t。
- 关键步骤：交错性给 Vandermonde 因子；反射行相关给 1-tz_az_b；剩余行因子；次数界与最低次齐次项定常数。
- 边界：n=1 时所有 pair product 为空。

#### L2.1.2.4

- 类型：statement；PDF 第 4 页；定位：(2.4)。
- 数学内容：\det[z_a^{n-r}-t^r z_a^{n+r}]=\prod_a(1-tz_a^2)N_t(z)。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant；N_t。
- 关键步骤：交错性给 Vandermonde 因子；反射行相关给 1-tz_az_b；剩余行因子；次数界与最低次齐次项定常数。
- 边界：n=1 时所有 pair product 为空。

#### L2.1.2.5

- 类型：statement；PDF 第 4 页；定位：(2.5)。
- 数学内容：\det[z_a^{n-r}+\tau^{2r-1}z_a^{n+r-1}]=\prod_a(1+\tau z_a)N_{\tau^2}(z)。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant；N_t。
- 关键步骤：交错性给 Vandermonde 因子；反射行相关给 1-tz_az_b；剩余行因子；次数界与最低次齐次项定常数。
- 边界：n=1 时所有 pair product 为空。

#### L2.1.first.alternating

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof。
- 数学内容：第 first 个行列式为交错多项式，含所有 z_a-z_b 因子。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant。

#### L2.1.first.reflection

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof first sentences。
- 数学内容：在 z_b=(tz_a)^{-1} 时，第 first 个行列式的 a,b 行成比例，论文所列乘子为 t^{1-n}z_a^{2-2n}；因此有 1-tz_az_b 因子。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant。
- 边界：在适当分式域中代入；不要求 t 数值非零的最终多项式恒等式。

#### L2.1.first.degree

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof degree display。
- 数学内容：第 first 个行列式的总次数上界为 3\binom n2，恰等于其列出的全部因子的总次数。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：degree。

#### L2.1.first.constant

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof last sentence。
- 数学内容：第 first 个行列式的最低次齐次部分为 \det[z_a^{n-r}]=\prod_{a<b}(z_a-z_b)，故剩余常数为 1。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：lowest homogeneous part。

#### L2.1.second.alternating

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof。
- 数学内容：第 second 个行列式为交错多项式，含所有 z_a-z_b 因子。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant。

#### L2.1.second.reflection

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof first sentences。
- 数学内容：在 z_b=(tz_a)^{-1} 时，第 second 个行列式的 a,b 行成比例，论文所列乘子为 -t^{-n}z_a^{-2n}；因此有 1-tz_az_b 因子。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant。
- 边界：在适当分式域中代入；不要求 t 数值非零的最终多项式恒等式。

#### L2.1.second.degree

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof degree display。
- 数学内容：第 second 个行列式的总次数上界为 2n+3\binom n2，恰等于其列出的全部因子的总次数。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：degree。

#### L2.1.second.constant

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof last sentence。
- 数学内容：第 second 个行列式的最低次齐次部分为 \det[z_a^{n-r}]=\prod_{a<b}(z_a-z_b)，故剩余常数为 1。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：lowest homogeneous part。

#### L2.1.third.alternating

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof。
- 数学内容：第 third 个行列式为交错多项式，含所有 z_a-z_b 因子。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant。

#### L2.1.third.reflection

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof first sentences。
- 数学内容：在 z_b=(tz_a)^{-1} 时，第 third 个行列式的 a,b 行成比例，论文所列乘子为 \tau^{1-2n}z_a^{1-2n}；因此有 1-tz_az_b 因子。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：alternant。
- 边界：在适当分式域中代入；不要求 t 数值非零的最终多项式恒等式。

#### L2.1.third.degree

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof degree display。
- 数学内容：第 third 个行列式的总次数上界为 n+3\binom n2，恰等于其列出的全部因子的总次数。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：degree。

#### L2.1.third.constant

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof last sentence。
- 数学内容：第 third 个行列式的最低次齐次部分为 \det[z_a^{n-r}]=\prod_{a<b}(z_a-z_b)，故剩余常数为 1。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：lowest homogeneous part。

#### L2.1.second.rowfactor

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof。
- 数学内容：第二个行列式第 a 行有因子 1-tz_a^2。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：row factor。

#### L2.1.third.rowfactor

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof。
- 数学内容：第三个行列式在 z_a=-\tau^{-1} 时为零，故第 a 行给因子 1+\tau z_a。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：row factor。

#### L2.1.Gauss

- 类型：proof_step；PDF 第 4 页；定位：Lemma 2.1 proof middle。
- 数学内容：可在剩余变量分式域验证整除，再用 Gauss 引理回到多项式环；上述各因子两两互素。
- 假设：n\ge1，1\le a,r\le n；z_a 与参数为独立变量；平方根第三式取 t=τ²。
- 对象：divisibility；polynomial ring。

### P2.2

#### P2.2.ratio.C0

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{C0}_{n,k}=\det(\Phi^CV^{C0})/\Delta_C。
- 假设：n,k\ge1；Table 1 的 C0 数据；继承 global 约定。
- 对象：P；V；C0。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.C0

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{C0}_H=1。
- 假设：n,k\ge1；Table 1 的 C0 数据。
- 对象：V_H；C0。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.ratio.Ct

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{Ct}_{n,k}=\det(\Phi^CV^{Ct})/\Delta_C。
- 假设：n,k\ge1；Table 1 的 Ct 数据；继承 global 约定。
- 对象：P；V；Ct。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.Ct

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{Ct}_H=1。
- 假设：n,k\ge1；Table 1 的 Ct 数据。
- 对象：V_H；Ct。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.ratio.BC

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{BC}_{n,k}=\det(\Phi^CV^{BC})/\Delta_C。
- 假设：n,k\ge1；Table 1 的 BC 数据；继承 global 约定。
- 对象：P；V；BC。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.BC

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{BC}_H=1。
- 假设：n,k\ge1；Table 1 的 BC 数据。
- 对象：V_H；BC。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.ratio.B0

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{B0}_{n,k}=\det(\Phi^BV^{B0})/\Delta_B。
- 假设：n,k\ge1；Table 1 的 B0 数据；继承 global 约定。
- 对象：P；V；B0。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.B0

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{B0}_H=1。
- 假设：n,k\ge1；Table 1 的 B0 数据。
- 对象：V_H；B0。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.ratio.Bminus

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{Bminus}_{n,k}=\det(\Phi^BV^{Bminus})/\Delta_B。
- 假设：n,k\ge1；Table 1 的 Bminus 数据；继承 global 约定。
- 对象：P；V；Bminus。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.Bminus

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{Bminus}_H=1。
- 假设：n,k\ge1；Table 1 的 Bminus 数据。
- 对象：V_H；Bminus。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.ratio.Bplus

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{Bplus}_{n,k}=\det(\Phi^+V^{Bplus})/\Delta_+。
- 假设：n,k\ge1；Table 1 的 Bplus 数据；继承 global 约定。
- 对象：P；V；Bplus。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.Bplus

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{Bplus}_H=1。
- 假设：n,k\ge1；Table 1 的 Bplus 数据。
- 对象：V_H；Bplus。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.ratio.Bt

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 first assertion。
- 数学内容：P^{Bt}_{n,k}=\det(\Phi^BV^{Bt})/\Delta_B。
- 假设：n,k\ge1；Table 1 的 Bt 数据；继承 global 约定。
- 对象：P；V；Bt。
- 关键步骤：WEYL.inversion.reduction；相应 alternant；对应有限折叠与分母符号抵消。

#### P2.2.minor.Bt

- 类型：statement；PDF 第 5 页；定位：Proposition 2.2 moreover。
- 数学内容：H=\{k+1,\ldots,k+n\} 时，\det V^{Bt}_H=1。
- 假设：n,k\ge1；Table 1 的 Bt 数据。
- 对象：V_H；Bt。
- 关键步骤：每列 r 的首项在 k+r 行系数 1；其余折叠行严格小于 k+r；unit upper triangular。
- 边界：k=0 时不可调用该 unit minor 结论。

#### P2.2.fold.C0

- 类型：proof_step；PDF 第 5 页；定位：Proposition 2.2 proof。
- 数学内容：C0 的行函数取 z^{-n-k}f_r(z)，按 g(z)-g(z^{-1}) 折叠后得到 -\Phi^C u^C_r。
- 假设：n,k\ge1；对应 Table 1 数据。
- 对象：C0；finite folding。
- 关键步骤：相应 (2.3)/(2.4)/(2.5)；分母对逆变换的变化。
- 边界：整个行列式的 n 个负号须与分母中的 (-1)^n 抵消。

#### P2.2.fold.BC

- 类型：proof_step；PDF 第 5 页；定位：Proposition 2.2 proof。
- 数学内容：BC 的行函数取 z^{-n-k}(1+\tau z)f_r(z)，按 g(z)-g(z^{-1}) 折叠后得到 -\Phi^C(u^C_r+\tau\widetilde u^C_r)。
- 假设：n,k\ge1；对应 Table 1 数据。
- 对象：BC；finite folding。
- 关键步骤：相应 (2.3)/(2.4)/(2.5)；分母对逆变换的变化。
- 边界：整个行列式的 n 个负号须与分母中的 (-1)^n 抵消。

#### P2.2.fold.Ct

- 类型：proof_step；PDF 第 5 页；定位：Proposition 2.2 proof。
- 数学内容：Ct 的行函数取 z^{-n-k}(z^{n-r}-t^r z^{n+r})，按 g(z)-g(z^{-1}) 折叠后得到 -\Phi^C([k+r]_C-t^r[k-r]_C)。
- 假设：n,k\ge1；对应 Table 1 数据。
- 对象：Ct；finite folding。
- 关键步骤：相应 (2.3)/(2.4)/(2.5)；分母对逆变换的变化。
- 边界：整个行列式的 n 个负号须与分母中的 (-1)^n 抵消。

#### P2.2.fold.B0

- 类型：proof_step；PDF 第 5 页；定位：Proposition 2.2 proof。
- 数学内容：B0 的行函数取 z^{-(n+k-1)}f_r(z)，按 g(z)-zg(z^{-1}) 折叠后得到 -\Phi^B u^B_r。
- 假设：n,k\ge1；对应 Table 1 数据。
- 对象：B0；finite folding。
- 关键步骤：相应 (2.3)/(2.4)/(2.5)；分母对逆变换的变化。
- 边界：整个行列式的 n 个负号须与分母中的 (-1)^n 抵消。

#### P2.2.fold.Bt

- 类型：proof_step；PDF 第 5 页；定位：Proposition 2.2 proof。
- 数学内容：Bt 的行函数取 z^{-(n+k-1)}(1-tz)f_r(z)，按 g(z)-zg(z^{-1}) 折叠后得到 -\Phi^B(u^B_r-t\widetilde u^B_r)。
- 假设：n,k\ge1；对应 Table 1 数据。
- 对象：Bt；finite folding。
- 关键步骤：相应 (2.3)/(2.4)/(2.5)；分母对逆变换的变化。
- 边界：整个行列式的 n 个负号须与分母中的 (-1)^n 抵消。

#### P2.2.fold.Bminus

- 类型：proof_step；PDF 第 6 页；定位：Proposition 2.2 proof。
- 数学内容：Bminus 的行函数取 z^{-(n+k-1)}(z^{n-r}+\tau^{2r-1}z^{n+r-1})，按 g(z)-zg(z^{-1}) 折叠后得到 -\Phi^B([k+r]_B+\tau^{2r-1}[k+1-r]_B)。
- 假设：n,k\ge1；对应 Table 1 数据。
- 对象：Bminus；finite folding。
- 关键步骤：相应 (2.3)/(2.4)/(2.5)；分母对逆变换的变化。
- 边界：整个行列式的 n 个负号须与分母中的 (-1)^n 抵消。

#### P2.2.fold.Bplus.first

- 类型：proof_step；PDF 第 6 页；定位：Proposition 2.2 proof B+ paragraph。
- 数学内容：B_+ 用 z^{-(n+k-1)}f_r(z) 和 g(z)+g(z^{-1})；第一列折叠为 C_k=\Phi^+[k+1]_+。
- 假设：n,k\ge1。
- 对象：Bplus；first column。
- 边界：没有额外的 even-orthogonal alternant 归一化。

#### P2.2.fold.Bplus.rest

- 类型：proof_step；PDF 第 6 页；定位：Proposition 2.2 proof B+ paragraph。
- 数学内容：B_+ 的第 r\ge2 列折叠为 C_{k+r-1}+t^{r-1}C_{k+1-r}=\Phi^+u^+_r。
- 假设：n,k\ge1，2\le r\le n。
- 对象：Bplus。

#### P2.2.triangular.leading

- 类型：proof_step；PDF 第 6 页；定位：Proposition 2.2 last paragraph。
- 数学内容：七种 case 的列 r 首 bracket 在 k+r 行放置系数 1。
- 假设：n,k\ge1，1\le r\le n。
- 对象：V。

#### P2.2.triangular.lower

- 类型：proof_step；PDF 第 6 页；定位：Proposition 2.2 last paragraph。
- 数学内容：k\ge1 时，列 r 其余项的所有折叠行均严格小于 k+r，包括原指标非正的项。
- 假设：n,k\ge1，1\le r\le n。
- 对象：V。
- 边界：k=0 另作列变换计算。

### T3.1

#### T3.1.transfer

- 类型：statement；PDF 第 6 页；定位：Theorem 3.1。
- 数学内容：\det(XY)=\dfrac{(-1)^{nk}\det X_{Q_0}\det Y_H}{\det U_J\det Z_I}\det(U^TZ)。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：X；Y；U；Z。
- 关键步骤：满秩与核空间同一；商空间顶次交替形式成比例；互补 minor 符号；Cauchy--Binet；在 Q0 和 H 定比例常数。
- 边界：结论包含 det(XY)=0 的情形；不假设 XY 可逆。

#### T3.1.rank.X

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof first sentence。
- 数学内容：非零 minor 使 rank X=n。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：X。

#### T3.1.rank.U

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof first sentence。
- 数学内容：非零 minor 使 rank U=k。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：U。

#### T3.1.kernel

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof first sentence。
- 数学内容：由 XU=0 及维数，\operatorname{col}(U)=\ker X。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：kernel；column space。

#### T3.1.topforms

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof forms display。
- 数学内容：(v_1,\ldots,v_n)\mapsto\det[Xv_1\cdots Xv_n] 与 (v_1,\ldots,v_n)\mapsto\det[U\ v_1\cdots v_n] 在 F^L/\operatorname{col}(U) 上诱导非零顶次交替形式，故成比例。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：alternating forms。

#### T3.1.epsilon

- 类型：definition；PDF 第 6 页；定位：Theorem 3.1 proof。
- 数学内容：Q=\{q_1<\cdots<q_n\} 时，\epsilon(Q)=(-1)^{\sum_{r=1}^n(q_r-r)}。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：epsilon；Q。

#### T3.1.complement.sign

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof Laplace display。
- 数学内容：\det[U\ e_{q_1}\cdots e_{q_n}]=(-1)^{nk}\epsilon(Q)\det U_{Q^c}。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：complementary minor。
- 关键步骤：沿最后 n 列 Laplace 展开。

#### T3.1.minors.X

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof proportional minors。
- 数学内容：存在与 Q 无关的常数 \alpha，\det X_Q=\alpha\epsilon(Q)\det U_{Q^c}。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：alpha；X；U。

#### T3.1.minors.Y

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof proportional minors。
- 数学内容：存在与 Q 无关的常数 \beta，\det Y_Q=\beta\epsilon(Q)\det Z_{Q^c}。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：beta；Y；Z。
- 关键步骤：对 Y^T Z=0 使用同样的互补最大 minor 比例。

#### T3.1.CauchyBinet

- 类型：proof_step；PDF 第 6 页；定位：Theorem 3.1 proof last display。
- 数学内容：\det(XY)=\alpha\beta\sum_{|Q|=n}\det U_{Q^c}\det Z_{Q^c}=\alpha\beta\det(U^TZ)。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：Cauchy--Binet。

#### T3.1.epsilon.Q0

- 类型：proof_step；PDF 第 7 页；定位：Theorem 3.1 proof end。
- 数学内容：\epsilon(Q_0)=1。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：epsilon。

#### T3.1.epsilon.H

- 类型：proof_step；PDF 第 7 页；定位：Theorem 3.1 proof end。
- 数学内容：\epsilon(H)=(-1)^{nk}。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：epsilon。

#### T3.1.alpha

- 类型：proof_step；PDF 第 7 页；定位：Theorem 3.1 proof end。
- 数学内容：\alpha=\det X_{Q_0}/\det U_J。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：alpha。

#### T3.1.beta

- 类型：proof_step；PDF 第 7 页；定位：Theorem 3.1 proof end。
- 数学内容：\beta=(-1)^{nk}\det Y_H/\det Z_I。
- 假设：F 为任意域；n,k\ge1；L=n+k；X\in F^{n\times L}，Y\in F^{L\times n}，U,Z\in F^{L\times k}；XU=0，Y^TZ=0；\det X_{Q_0}\ne0，\det U_J\ne0，\det Y_H\ne0，\det Z_I\ne0；采用递增子集、行列 minor 的 global 约定。
- 对象：beta。

#### T3.1.normalized

- 类型：statement；PDF 第 7 页；定位：(3.1)。
- 数学内容：若 \Phi D=0，V^TC=0 且 \det D_J\det C_I\ne0，则 P^\star_{n,k}=\dfrac{(-1)^{nk}}{\det D_J\det C_I}\det(D^TC)。
- 假设：n,k\ge1；Table 1 的任一 case；\det\Phi_{Q_0}=\Delta；\det V_H=1；\Phi D=0，V^TC=0，\det D_J\ne0，\det C_I\ne0；相应有理函数系数域。
- 对象：P；D；C；V。
- 关键步骤：T3.1.transfer；P2.2 各 case ratio/minor；消去 Delta。
- 边界：只需两个指定互补 minor；不可遗漏任一非零条件。

### L3.2

#### L3.2.symmetry.Lambda

- 类型：statement；PDF 第 7 页；定位：(3.2)。
- 数学内容：\Lambda_i(-m)=-\Lambda_i(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Lambda。
- 关键步骤：COEFF.edot.palindrome；对应行核定义。

#### L3.2.symmetry.h

- 类型：statement；PDF 第 7 页；定位：(3.2)。
- 数学内容：h_i(1-m)=h_i(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：h。
- 关键步骤：COEFF.edot.palindrome；对应行核定义。

#### L3.2.symmetry.hplus

- 类型：statement；PDF 第 7 页；定位：(3.2)。
- 数学内容：h_i^+(2-m)=h_i^+(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：hplus。
- 关键步骤：COEFF.edot.palindrome；对应行核定义。

#### L3.2.palindrome.form.h

- 类型：statement；PDF 第 7 页；定位：(3.2)后。
- 数学内容：h_i(m)=\dot e_{n-i+m}+\dot e_{n-i-m+1}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：h。

#### L3.2.palindrome.form.hplus

- 类型：statement；PDF 第 7 页；定位：(3.2)后。
- 数学内容：h_i^+(m)=\dot e_{n-i+m}+\dot e_{n-i-m+2}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：hplus。

#### L3.2.D.C

- 类型：definition；PDF 第 7 页；定位：(3.3)。
- 数学内容：D^C_{p,i}=(-1)^p\Lambda_i(p)，矩阵大小为 L×k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：DC。

#### L3.2.D.B

- 类型：definition；PDF 第 7 页；定位：(3.3)。
- 数学内容：D^B_{p,i}=(-1)^ph_i(p)，矩阵大小为 L×k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：DB。

#### L3.2.D.plus

- 类型：definition；PDF 第 7 页；定位：(3.3)。
- 数学内容：D^+_{p,i}=(-1)^ph_i^+(p)，矩阵大小为 L×k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Dplus。

#### L3.2.kernel.C

- 类型：statement；PDF 第 7 页；定位：Lemma 3.2 first assertion。
- 数学内容：\Phi^CD^C=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：\Phi^C；D^C。
- 关键步骤：生成函数在 -x_a 消失；按相应整数反射配对；p>L 支撑消失。

#### L3.2.minor.C

- 类型：statement；PDF 第 7 页；定位：Lemma 3.2 complementary minors。
- 数学内容：\det D^C_J=\zeta。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^C；J。
- 关键步骤：末 k 行的显式公式；上三角块的对角乘积。
- 边界：k=1 仍成立。

#### L3.2.kernel.B

- 类型：statement；PDF 第 7 页；定位：Lemma 3.2 first assertion。
- 数学内容：\Phi^BD^B=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：\Phi^B；D^B。
- 关键步骤：生成函数在 -x_a 消失；按相应整数反射配对；p>L 支撑消失。

#### L3.2.minor.B

- 类型：statement；PDF 第 7 页；定位：Lemma 3.2 complementary minors。
- 数学内容：\det D^B_J=\zeta。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B；J。
- 关键步骤：末 k 行的显式公式；上三角块的对角乘积。
- 边界：k=1 仍成立。

#### L3.2.kernel.plus

- 类型：statement；PDF 第 7 页；定位：Lemma 3.2 first assertion。
- 数学内容：\Phi^+D^+=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：\Phi^+；D^+。
- 关键步骤：生成函数在 -x_a 消失；按相应整数反射配对；p>L 支撑消失。
- 边界：D^+ 第一行没有额外因子 2。。

#### L3.2.minor.plus

- 类型：statement；PDF 第 7 页；定位：Lemma 3.2 complementary minors。
- 数学内容：\det D^+_J=2\zeta。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^+；J。
- 关键步骤：末 k 行的显式公式；上三角块的对角乘积。
- 边界：k=1 时唯一对角项为 2(-1)^{n+1}。。

#### L3.2.generating.C

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof generating identities。
- 数学内容：\sum_{m\in\mathbb Z}\Lambda_i(m)z^m=z^{-n}\dot E(z)(z^i-z^{-i})。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：generating function；C。
- 关键步骤：重新编号有限系数和；palindromicity。
- 边界：Laurent 多项式；整数和有限。

#### L3.2.generating.vanish.C

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof。
- 数学内容：C 生成函数在 z=-x_a 处为零。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：generating function；C。
- 关键步骤：\dot E(-x_a)=0，因 (1+zx_a^{-1}) 因子为零。

#### L3.2.generating.B

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof generating identities。
- 数学内容：\sum_{m\in\mathbb Z}h_i(m)z^m=z^{-n}\dot E(z)(z^i+z^{1-i})。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：generating function；B。
- 关键步骤：重新编号有限系数和；palindromicity。
- 边界：Laurent 多项式；整数和有限。

#### L3.2.generating.vanish.B

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof。
- 数学内容：B 生成函数在 z=-x_a 处为零。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：generating function；B。
- 关键步骤：\dot E(-x_a)=0，因 (1+zx_a^{-1}) 因子为零。

#### L3.2.generating.plus

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof generating identities。
- 数学内容：\sum_{m\in\mathbb Z}h_i^+(m)z^m=z^{-n}\dot E(z)(z^i+z^{2-i})。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：generating function；plus。
- 关键步骤：重新编号有限系数和；palindromicity。
- 边界：Laurent 多项式；整数和有限。

#### L3.2.generating.vanish.plus

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof。
- 数学内容：plus 生成函数在 z=-x_a 处为零。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：generating function；plus。
- 关键步骤：\dot E(-x_a)=0，因 (1+zx_a^{-1}) 因子为零。

#### L3.2.pair.C

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof pair sums。
- 数学内容：m\leftrightarrow-m 配对生成函数在 -x_a 的值，得到 \sum_{p\ge1}(-1)^p\Lambda_i(p)\phi_p(x_a)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C kernel。
- 边界：固定点 m=0 的 Lambda_i(0)=0。。

#### L3.2.pair.B

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof pair sums。
- 数学内容：m\leftrightarrow1-m 配对生成函数在 -x_a 的值，得到 \sum_{p\ge1}(-1)^ph_i(p)\psi_p(x_a)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B kernel。

#### L3.2.pair.plus

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof fixed-center display。
- 数学内容：m\leftrightarrow2-m 配对后除以 x_a，得到 -h_i^+(1)+\sum_{p\ge2}(-1)^ph_i^+(p)C_{p-1}(x_a)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：plus kernel。
- 边界：固定点 m=1 只出现一次。。

#### L3.2.support.C

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof all kernels vanish。
- 数学内容：对 p>L，\Lambda_i(p)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：\Lambda_i。
- 关键步骤：系数零延拓；1≤i≤k，L=n+k。

#### L3.2.support.B

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof all kernels vanish。
- 数学内容：对 p>L，h_i(p)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：h_i。
- 关键步骤：系数零延拓；1≤i≤k，L=n+k。

#### L3.2.support.plus

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof all kernels vanish。
- 数学内容：对 p>L，h_i^+(p)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：h_i^+。
- 关键步骤：系数零延拓；1≤i≤k，L=n+k。

#### L3.2.lastblock.C

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof last display。
- 数学内容：D^C_{n+r,i}=(-1)^{n+r}\dot e_{i-r}，1≤r,i≤k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D_J。

#### L3.2.lastblock.B

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof last display。
- 数学内容：D^B_{n+r,i}=(-1)^{n+r}\dot e_{i-r}，1≤r,i≤k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D_J。

#### L3.2.lastblock.plus

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof last display。
- 数学内容：D^+_{n+r,i}=(-1)^{n+r}(\dot e_{i-r}+\dot e_{2-i-r})，1≤r,i≤k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D_J。

#### L3.2.triangular.C

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof last paragraph。
- 数学内容：D^C_J 为上三角，对角 (-1)^{n+r}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D_J。
- 边界：由 dot e_0=1 与负下标为零计算。

#### L3.2.triangular.B

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof last paragraph。
- 数学内容：D^B_J 为上三角，对角 (-1)^{n+r}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D_J。
- 边界：由 dot e_0=1 与负下标为零计算。

#### L3.2.triangular.plus

- 类型：proof_step；PDF 第 7 页；定位：Lemma 3.2 proof last paragraph。
- 数学内容：D^+_J 为上三角；第一对角项 2(-1)^{n+1}，其余为 (-1)^{n+r}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D_J。
- 边界：由 dot e_0=1 与负下标为零计算。

### L3.3

#### L3.3.fold.C

- 类型：definition；PDF 第 8 页；定位：(3.4)。
- 数学内容：C^C(b)_{p,j}=b_j(p)-b_j(-p)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C(b)；b_j。

#### L3.3.fold.B

- 类型：definition；PDF 第 8 页；定位：(3.4)。
- 数学内容：C^B(b)_{p,j}=(-1)^p(b_j(p)+b_j(1-p))。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C(b)；b_j。

#### L3.3.fold.plus.center

- 类型：definition；PDF 第 8 页；定位：(3.4)。
- 数学内容：C^+(b)_{1,j}=-b_j(1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C(b)；b_j。
- 边界：中心行不是 -2b_j(1)。。

#### L3.3.fold.plus.rest

- 类型：definition；PDF 第 8 页；定位：(3.4)。
- 数学内容：C^+(b)_{p,j}=(-1)^p(b_j(p)+b_j(2-p)),\ 2\le p\le L。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C(b)；b_j。

#### L3.3.unfold.C

- 类型：statement；PDF 第 8 页；定位：(3.5)。
- 数学内容：((D^C)^TC^C(b))_{ij}=\sum_{m\in\mathbb Z}(-1)^m\Lambda_i(m)b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^C；C^C；b。
- 关键步骤：m=p 与 m=-p 配对；Lambda_i(0)=0；p>L 支撑为零。

#### L3.3.unfold.B

- 类型：statement；PDF 第 8 页；定位：(3.6)。
- 数学内容：((D^B)^TC^B(b))_{ij}=\sum_{m\in\mathbb Z}h_i(m)b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B；C^B；b。
- 关键步骤：p≥1 与 1-p≤0 配对；p>L 支撑为零。

#### L3.3.unfold.plus

- 类型：statement；PDF 第 8 页；定位：(3.7)。
- 数学内容：((D^+)^TC^+(b))_{ij}=\sum_{m\in\mathbb Z}h_i^+(m)b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^+；C^+；b。
- 关键步骤：中心单次项；p≥2 与 2-p≤0 配对；p>L 支撑为零。
- 边界：序列 b 可无穷支撑；与行核的乘积有有限支撑。

#### L3.3.center.once

- 类型：proof_step；PDF 第 8 页；定位：Lemma 3.3 proof。
- 数学内容：(D^+)_{1,i}C^+(b)_{1,j}=h_i^+(1)b_j(1)，故固定中心恰计一次。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：fixed center。
- 边界：D 第一行与 C 第一行均带负号；不增加倍数 2。

### P4.1

#### P4.1.K.C0

- 类型：definition；PDF 第 9 页；定位：Proposition 4.1 proof first line。
- 数学内容：C0 取 K=2k+2。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：K；C0。

#### P4.1.K.BC

- 类型：definition；PDF 第 9 页；定位：Proposition 4.1 proof first line。
- 数学内容：BC 取 K=2k+1。并取 t=τ²。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：K；BC。

#### P4.1.b.residue

- 类型：definition；PDF 第 9 页；定位：Proposition 4.1 sequence display。
- 数学内容：m=j+Kq，q\in\mathbb Z 时，b_j(m)=t^{Kq^2/2+jq}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。
- 边界：K>0 保证 q 唯一；BC 用 tau 约定解释半幂。

#### P4.1.b.outside

- 类型：definition；PDF 第 9 页；定位：Proposition 4.1 sequence display。
- 数学内容：m\not\equiv j\pmod K 时，b_j(m)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### P4.1.c

- 类型：definition；PDF 第 9 页；定位：Proposition 4.1 sequence display。
- 数学内容：c_j(m)=b_j(m)-b_j(-m)，C=C^C(b)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j；C。

#### P4.1.quasiperiod

- 类型：proof_step；PDF 第 9 页；定位：before (4.1)。
- 数学内容：b_j(m+K)=t^{m+K/2}b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。
- 关键步骤：q→q+1。
- 边界：非支撑剩余类两端均零。

#### P4.1.reflection.odd

- 类型：proof_step；PDF 第 9 页；定位：(4.1) first。
- 数学内容：c_j(-m)=-c_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j。

#### P4.1.reflection.affine

- 类型：proof_step；PDF 第 9 页；定位：(4.1) second。
- 数学内容：c_j(m)+t^{m-K/2}c_j(K-m)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j。
- 关键步骤：对 b_j(K-m)、b_j(m-K) 使用准周期。
- 边界：所有整数 m，包含支撑类之外。

#### P4.1.C0.firstcolumn

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 proof C0。
- 数学内容：K=2k+2 时 c_j(k+1)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C0；c_j。
- 关键步骤：反射固定点的特征值为 -1；特征零中 2 非零。

#### P4.1.C0.restcolumns

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 proof C0。
- 数学内容：K=2k+2 时，c_j(k+r)+t^{r-1}c_j(k+2-r)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C0；c_j。
- 关键步骤：m=k+r 代入仿射反射。

#### P4.1.C0.kernel

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 proof C0。
- 数学内容：(V^{C0})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：V；C；C0。
- 关键步骤：c 的奇延拓与 [m]_C 评估一致；首列消失；其余列反射消失。

#### P4.1.BC.firstcolumn

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 proof BC。
- 数学内容：K=2k+1、t=τ² 时，c_j(k+1)+\tau c_j(k)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：BC；c_j。
- 关键步骤：m=k+1 代入仿射反射。

#### P4.1.BC.restcolumns

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 four-term display。
- 数学内容：r\ge2，h=k+r 时，(v_r^{BC})^TC_{\bullet,j}=[c_j(h)+\tau^{2h-K}c_j(K-h)]+\tau[c_j(h-1)+\tau^{2(h-1)-K}c_j(K-h+1)]=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：BC；four-term reflection。
- 关键步骤：各方括号由仿射反射分别为零。

#### P4.1.BC.kernel

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 proof BC。
- 数学内容：(V^{BC})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：V；C；BC。
- 关键步骤：首列反射；其余四项分组反射。

#### P4.1.residues.disjoint

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 after column calculation。
- 数学内容：K>2k，故初始 k 行中的 j 与 -j 剩余类互不重合。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：residue classes。
- 边界：j=k 也不重合。

#### P4.1.CI.entries

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 complementary block。
- 数学内容：C_I=I_k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。
- 关键步骤：b_j(p)=δ_pj；b_j(-p)=0，1≤p,j≤k。

#### P4.1.CI.det

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 complementary block。
- 数学内容：\det C_I=1。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P4.1.A

- 类型：definition；PDF 第 9 页；定位：Proposition 4.1 pairing display。
- 数学内容：A_{ij}=\sum_{y\in\mathbb Z}(-1)^{Ky}t^{Ky^2/2-jy}\Lambda_i(j-Ky)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A。

#### P4.1.pairing

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 pairing display。
- 数学内容：(D^C)^TC=A\operatorname{diag}((-1)^1,\ldots,(-1)^k)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^C；C；A。
- 关键步骤：L3.3.unfold.C；y=-q；(-1)^{j-Ky}=(-1)^j(-1)^{Ky}。

#### P4.1.sign.C0

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 final paragraph。
- 数学内容：C0 中 (-1)^{Ky}=1。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C0；affine sign。

#### P4.1.det.C0

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 final paragraph。
- 数学内容：P^{C0}_{n,k}=\det A。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C0；P；A。
- 关键步骤：T3.1.normalized；det D_J=ζ；det C_I=1；det column sign=ω；ζ=(-1)^{nk}ω。

#### P4.1.C0.result

- 类型：statement；PDF 第 9 页；定位：Proposition 4.1 statement。
- 数学内容：等式 (1.6) 对 n,k≥1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C0。
- 关键步骤：P4.1.det.C0；AFFINE.multilinearity。

#### P4.1.sign.BC

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 final paragraph。
- 数学内容：BC 中 (-1)^{Ky}=(-1)^y。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：BC；affine sign。

#### P4.1.det.BC

- 类型：proof_step；PDF 第 9 页；定位：Proposition 4.1 final paragraph。
- 数学内容：P^{BC}_{n,k}=\det A。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：BC；P；A。
- 关键步骤：T3.1.normalized；det D_J=ζ；det C_I=1；det column sign=ω；ζ=(-1)^{nk}ω。

#### P4.1.BC.result

- 类型：statement；PDF 第 9 页；定位：Proposition 4.1 statement。
- 数学内容：等式 (1.8) 对 n,k≥1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：BC。
- 关键步骤：P4.1.det.BC；AFFINE.multilinearity。

### P4.2

#### P4.2.K.B0

- 类型：definition；PDF 第 9 页；定位：Proposition 4.2 proof first line。
- 数学内容：B0 取 K=2k+1。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：K；B0。

#### P4.2.K.Bminus

- 类型：definition；PDF 第 9 页；定位：Proposition 4.2 proof first line。
- 数学内容：Bminus 取 K=2k。并取 t=τ²。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：K；Bminus。

#### P4.2.b.residue

- 类型：definition；PDF 第 9 页；定位：Proposition 4.2 sequence display。
- 数学内容：m=j-Ky，y\in\mathbb Z 时，b_j(m)=(-1)^{Ky}t^{Ky^2/2-(j-1/2)y}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### P4.2.b.outside

- 类型：definition；PDF 第 9 页；定位：Proposition 4.2 sequence display。
- 数学内容：m\not\equiv j\pmod K 时，b_j(m)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### P4.2.gamma

- 类型：definition；PDF 第 9 页；定位：Proposition 4.2 bottom display。
- 数学内容：\gamma_j(m)=(-1)^m(b_j(m)+b_j(1-m))，C=C^B(b)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma_j；C。

#### P4.2.quasiperiod

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 proof first sentence。
- 数学内容：b_j(m+K)=(-1)^Kt^{m+(K-1)/2}b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。
- 关键步骤：y→y-1。
- 边界：所有整数 m，支撑类之外为零。

#### P4.2.reflection.finite

- 类型：proof_step；PDF 第 10 页；定位：(4.2) first。
- 数学内容：\gamma_j(1-m)=-\gamma_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma。

#### P4.2.reflection.affine

- 类型：proof_step；PDF 第 10 页；定位：(4.2) second。
- 数学内容：\gamma_j(m)=-t^{m-(K+1)/2}\gamma_j(K+1-m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma。
- 关键步骤：对两反射项使用准周期；gamma 定义中的奇偶使 K 奇偶均保留负号。

#### P4.2.reflection.factor

- 类型：proof_step；PDF 第 10 页；定位：(4.2)后 example。
- 数学内容：b_j(K+1-m)、b_j(m-K) 分别从 b_j(1-m)、b_j(m) 获得因子 (-1)^Kt^{(K+1)/2-m}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j；reflection factor。

#### P4.2.B0.firstcolumn

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 B0 paragraph。
- 数学内容：B_0 的固定点 m=k+1 给 \gamma_j(k+1)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0；gamma。

#### P4.2.B0.restcolumns

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 B0 paragraph。
- 数学内容：B_0 中 \gamma_j(k+r)+t^{r-1}\gamma_j(k+2-r)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0；gamma。

#### P4.2.Bminus.columns

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 Bminus paragraph。
- 数学内容：B_- 中 \gamma_j(k+r)+\tau^{2r-1}\gamma_j(k+1-r)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bminus；gamma。

#### P4.2.kernel.B0

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 kernel relation。
- 数学内容：(V^{B0})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0；V；C。
- 关键步骤：有限反射使 [m]_B 评估等于 gamma(m)；对应列关系。

#### P4.2.kernel.Bminus

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 kernel relation。
- 数学内容：(V^{Bminus})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bminus；V；C。
- 关键步骤：有限反射使 [m]_B 评估等于 gamma(m)；对应列关系。

#### P4.2.CI.direct

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 first k rows。
- 数学内容：1≤p,j≤k 时，b_j(p)=\delta_{p,j}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j；C_I。

#### P4.2.CI.reflected

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 first k rows。
- 数学内容：1≤p,j≤k 时，b_j(1-p)=0，因为 1≤j+p-1≤2k-1<K。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j；C_I。
- 边界：K=2k，k=1 仍满足。

#### P4.2.CI.entries

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 first k rows。
- 数学内容：C_I=\operatorname{diag}((-1)^1,\ldots,(-1)^k)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P4.2.CI.det

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 first k rows。
- 数学内容：\det C_I=\omega。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P4.2.A

- 类型：definition；PDF 第 10 页；定位：Proposition 4.2 pairing display。
- 数学内容：A_{ij}=\sum_{y\in\mathbb Z}(-1)^{Ky}t^{Ky^2/2-(j-1/2)y}h_i(j-Ky)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A。

#### P4.2.pairing

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 pairing display。
- 数学内容：(D^B)^TC=A。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B；C；A。
- 关键步骤：L3.3.unfold.B；序列的唯一支撑参数 y。

#### P4.2.sign.B0

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 final paragraph。
- 数学内容：B0 中 (-1)^{Ky}=(-1)^y。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0；affine sign。

#### P4.2.det.B0

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 final paragraph。
- 数学内容：P^{B0}_{n,k}=\det A。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0；P；A。
- 关键步骤：T3.1.normalized；det D_J=ζ；det C_I=ω；ζ=(-1)^{nk}ω。

#### P4.2.B0.result

- 类型：statement；PDF 第 9 页；定位：Proposition 4.2 statement。
- 数学内容：等式 (1.3) 对 n,k≥1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0。
- 关键步骤：P4.2.det.B0；AFFINE.multilinearity。

#### P4.2.sign.Bminus

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 final paragraph。
- 数学内容：Bminus 中 (-1)^{Ky}=1。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bminus；affine sign。

#### P4.2.det.Bminus

- 类型：proof_step；PDF 第 10 页；定位：Proposition 4.2 final paragraph。
- 数学内容：P^{Bminus}_{n,k}=\det A。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bminus；P；A。
- 关键步骤：T3.1.normalized；det D_J=ζ；det C_I=ω；ζ=(-1)^{nk}ω。

#### P4.2.Bminus.result

- 类型：statement；PDF 第 9 页；定位：Proposition 4.2 statement。
- 数学内容：等式 (1.4) 对 n,k≥1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bminus。
- 关键步骤：P4.2.det.Bminus；AFFINE.multilinearity。

### P5.1

#### P5.1.K

- 类型：definition；PDF 第 10 页；定位：Proposition 5.1 proof first line。
- 数学内容：K=2k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：K；Ct。

#### P5.1.b.residue

- 类型：definition；PDF 第 10 页；定位：Proposition 5.1 sequence display。
- 数学内容：m=j+2kq，q\in\mathbb Z 时，b_j(m)=(-1)^q t^{kq^2+jq}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### P5.1.b.outside

- 类型：definition；PDF 第 10 页；定位：Proposition 5.1 sequence display。
- 数学内容：m\not\equiv j\pmod{2k} 时，b_j(m)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### P5.1.c

- 类型：definition；PDF 第 10 页；定位：Proposition 5.1 after sequence display。
- 数学内容：c_j(m)=b_j(m)-b_j(-m)，C=C^C(b)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j；C。

#### P5.1.quasiperiod

- 类型：proof_step；PDF 第 10 页；定位：Proposition 5.1 proof。
- 数学内容：b_j(m+2k)=-t^{m+k}b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。
- 关键步骤：q→q+1。
- 边界：全体整数 m；支撑外双方均零。

#### P5.1.reflection.odd

- 类型：proof_step；PDF 第 10 页；定位：Proposition 5.1 reflection display。
- 数学内容：c_j(-m)=-c_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j。

#### P5.1.reflection.affine

- 类型：proof_step；PDF 第 10 页；定位：Proposition 5.1 reflection display。
- 数学内容：c_j(m)=t^{m-k}c_j(2k-m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j。
- 关键步骤：带负号准周期使普通反射中的负号改变。

#### P5.1.column

- 类型：proof_step；PDF 第 10 页；定位：Proposition 5.1 after reflections。
- 数学内容：c_j(k+r)-t^r c_j(k-r)=0，故 [k+r]_C-t^r[k-r]_C 的评估消失。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Ct；finite column。

#### P5.1.kernel

- 类型：proof_step；PDF 第 10 页；定位：Proposition 5.1 after reflections。
- 数学内容：(V^{Ct})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：V；C；Ct。
- 关键步骤：P5.1.column；c 的奇延拓与 C bracket 一致。

#### P5.1.fixed.residue

- 类型：proof_step；PDF 第 10 页；定位：Proposition 5.1 last display。
- 数学内容：c_k(k+2kq)=2(-1)^q t^{kq(q+1)}，q\in\mathbb Z。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：fixed residue；c_k。
- 关键步骤：k 与 -k 模 2k 重合；反射支撑参数 -q-1；两项符号相反，作差后相加。
- 边界：重合不导致抵消，而导致倍数 2。

#### P5.1.nonfixed.residue

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 first line。
- 数学内容：j<k 时，j 与 -j 模 2k 的两个剩余类仍互不重合。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：residues。
- 边界：k=1 时此条件范围为空。

#### P5.1.CI.entries

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 complementary block。
- 数学内容：C_I=\operatorname{diag}(1,\ldots,1,2)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。
- 关键步骤：非固定剩余类给单位项；固定剩余类 k 给 2。
- 边界：k=1 时 C_I=[2]。

#### P5.1.CI.det

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 complementary block。
- 数学内容：\det C_I=2。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。
- 边界：k=1 包含在内。

#### P5.1.a

- 类型：definition；PDF 第 11 页；定位：Proposition 5.1 a,A± display。
- 数学内容：a_{ij}(y)=t^{ky^2-jy}\Lambda_i(j-2ky)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：a_ij。

#### P5.1.Aplus

- 类型：definition；PDF 第 11 页；定位：Proposition 5.1 a,A± display。
- 数学内容：A^+_{ij}=\sum_y a_{ij}(y)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A^+。

#### P5.1.Aminus

- 类型：definition；PDF 第 11 页；定位：Proposition 5.1 a,A± display。
- 数学内容：A^-_{ij}=\sum_y(-1)^y a_{ij}(y)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A^-。

#### P5.1.pairing

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 pairing sentence。
- 数学内容：(D^C)^TC=A^-\operatorname{diag}((-1)^1,\ldots,(-1)^k)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^C；C；A^-。
- 关键步骤：L3.3.unfold.C；y=-q；2k 为偶数。

#### P5.1.halfdet

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 pairing sentence。
- 数学内容：P^{Ct}_{n,k}=\tfrac12\det A^-。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：P；A^-。
- 关键步骤：T3.1.normalized；det D_J=ζ；det C_I=2；列符号 determinant=ω。

#### P5.1.parity.projector

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 parity paragraph。
- 数学内容：偶和子格指示函数为 \mathbf1_{\sum_i y_i\in2\mathbb Z}=\tfrac12(1+(-1)^{\sum_i y_i})。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：parity projector。
- 边界：特征零系数域中 1/2 有意义。

#### P5.1.parity.det

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 parity display。
- 数学内容：\sum_{y\in\mathbb Z^k_{\mathrm{even}}}\det[a_{ij}(y_i)]=\tfrac12(\det A^++\det A^-)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：even lattice；A^+；A^-。
- 关键步骤：P5.1.parity.projector；AFFINE.multilinearity。
- 边界：符号 (-1)^{sum y_i} 由行权重相乘产生。

#### P5.1.lastcolumn.exponent

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 final paragraph。
- 数学内容：末列 j=k 中，y\mapsto1-y 保持 ky^2-ky 不变。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：last column；involution。

#### P5.1.lastcolumn.argument

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 final paragraph。
- 数学内容：末列 j=k 中，y\mapsto1-y 把 k-2ky 变为其相反数。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：last column；involution。

#### P5.1.lastcolumn.antisymmetry

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 final paragraph。
- 数学内容：a_{i,k}(1-y)=-a_{i,k}(y)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：a；last column。
- 关键步骤：P5.1.lastcolumn.exponent；P5.1.lastcolumn.argument；Lambda 奇性。

#### P5.1.lastcolumn.zero

- 类型：proof_step；PDF 第 11 页；定位：Proposition 5.1 final paragraph。
- 数学内容：A^+ 的最后一列为零，因此 \det A^+=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A^+。
- 关键步骤：y→1-y 是整数上的无固定点对合；有限和的反对称配对。
- 边界：k=1 仍有末列且行和为零。

#### P5.1.result

- 类型：statement；PDF 第 10 页；定位：Proposition 5.1 statement。
- 数学内容：等式 (1.7) 对 n,k\ge1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Ct；even lattice。
- 关键步骤：P5.1.halfdet；P5.1.parity.det；P5.1.lastcolumn.zero。
- 边界：结论的求和域是偶和子格，不能替换为全格和。

### L5.2

#### L5.2.b.residue

- 类型：definition；PDF 第 11 页；定位：(5.1) first branch。
- 数学内容：m=j-2ky，y\in\mathbb Z 时，b_j(m)=(-1)^y t^{ky^2-(j-1)y}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### L5.2.b.outside

- 类型：definition；PDF 第 11 页；定位：(5.1) second branch。
- 数学内容：m\not\equiv j\pmod{2k} 时，b_j(m)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### L5.2.Gamma

- 类型：definition；PDF 第 11 页；定位：(5.1) second line。
- 数学内容：\Gamma_j(m)=(-1)^m(b_j(m)+b_j(2-m))。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Gamma；b_j。

#### L5.2.quasiperiod

- 类型：statement；PDF 第 11 页；定位：(5.2) first。
- 数学内容：b_j(m+2k)=-t^{m+k-1}b_j(m)，对所有 m\in\mathbb Z。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。
- 关键步骤：y→y-1。
- 边界：支撑外双方为零。

#### L5.2.symmetry

- 类型：statement；PDF 第 11 页；定位：(5.2) second。
- 数学内容：\Gamma_j(2-m)=\Gamma_j(m)，对所有 m\in\mathbb Z。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Gamma。
- 关键步骤：定义；m 与 2-m 同奇偶。

#### L5.2.reflection

- 类型：statement；PDF 第 11 页；定位：(5.2) third。
- 数学内容：\Gamma_j(m)=-t^{m-k-1}\Gamma_j(2k+2-m)，对所有 m\in\mathbb Z。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Gamma。
- 关键步骤：L5.2.shift.reflected；L5.2.shift.backward；m 与 2k+2-m 同奇偶。
- 边界：指数可能为负；分式域证明。

#### L5.2.fixedcenter

- 类型：statement；PDF 第 11 页；定位：Lemma 5.2 in particular。
- 数学内容：\Gamma_j(k+1)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Gamma；fixed center。
- 关键步骤：m=k+1；反射特征值 -1；特征零中除以 2。

#### L5.2.shift.reflected

- 类型：proof_step；PDF 第 11 页；定位：Lemma 5.2 proof display。
- 数学内容：b_j(2k+2-m)=-t^{k+1-m}b_j(2-m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

#### L5.2.shift.backward

- 类型：proof_step；PDF 第 11 页；定位：Lemma 5.2 proof display。
- 数学内容：b_j(m-2k)=-t^{k+1-m}b_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j。

### P5.3

#### P5.3.C

- 类型：definition；PDF 第 12 页；定位：Proposition 5.3 first sentence。
- 数学内容：C=C^+(b)，其中 b 取 (5.1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C；b_j。

#### P5.3.center.eval

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first display。
- 数学内容：[1]_+^TC_{\bullet,j}=2C_{1,j}=-2b_j(1)=\Gamma_j(1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：center；bracket。
- 关键步骤：[1]_+=2e1；C1j=-bj(1)。
- 边界：bracket 中的 2 与标准化中心行必须同时保留。

#### P5.3.bracket.eval

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 after first display。
- 数学内容：每个允许的 bracket [m]_+ 对 C_{\bullet,j} 的评估均为 \Gamma_j(m)，包含 m=1 的固定中心。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：bracket；Gamma。
- 关键步骤：P5.3.center.eval；L5.2.symmetry；C+ 的非中心行定义。

#### P5.3.firstcolumn

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first paragraph。
- 数学内容：第一列 u^+_1 对 C 的评估为 \Gamma_j(k+1)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bplus；first column。

#### P5.3.restcolumns

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first paragraph。
- 数学内容：r\ge2 时，u^+_r 对 C 的评估为 \Gamma_j(k+r)+t^{r-1}\Gamma_j(k+2-r)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bplus；columns。
- 关键步骤：L5.2.reflection 于 m=k+r。

#### P5.3.kernel

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first paragraph。
- 数学内容：(V^{Bplus})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：V；C。
- 关键步骤：P5.3.firstcolumn；P5.3.restcolumns。

#### P5.3.CI.center

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first k rows。
- 数学内容：b_j(1)=\delta_{j,1}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j；C_I。

#### P5.3.CI.direct

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first k rows。
- 数学内容：2≤p≤k 时，b_j(p)=\delta_{p,j}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j；C_I。
- 边界：k=1 该范围为空。

#### P5.3.CI.reflected

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first k rows。
- 数学内容：2≤p≤k 时，b_j(2-p)=0；相应同余要求 2ky=j+p-2\in\{1,\ldots,2k-2\}，不可能。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：b_j；C_I。
- 边界：k=1 不需此项。

#### P5.3.CI.entries

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first k rows。
- 数学内容：C_I=\operatorname{diag}((-1)^1,\ldots,(-1)^k)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P5.3.CI.det

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 first k rows。
- 数学内容：\det C_I=\omega。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P5.3.doubling.location

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 second paragraph。
- 数学内容：倍数 2 位于 \det D^+_J=2\zeta，其首对角系数来自 \dot e_0+\dot e_0；它不位于 \det C_I。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^+_J；C_I。
- 关键步骤：L3.2.lastblock.plus；L3.2.minor.plus。
- 边界：k=1 时也如此。

#### P5.3.A

- 类型：definition；PDF 第 12 页；定位：Proposition 5.3 pairing display。
- 数学内容：A^{Bplus}_{ij}=\sum_y(-1)^y t^{ky^2-(j-1)y}h_i^+(j-2ky)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A。

#### P5.3.pairing

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 pairing display。
- 数学内容：(D^+)^TC=A^{Bplus}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^+；C；A。
- 关键步骤：L3.3.unfold.plus；(5.1)。

#### P5.3.pairing.center.once

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 final paragraph。
- 数学内容：该配对的中心项正好为 h_i^+(1)b_j(1)，系数没有加倍。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：pairing center。
- 边界：不得将 D_J 的倍数 2 再放到配对中心。

#### P5.3.halfdet

- 类型：proof_step；PDF 第 12 页；定位：Proposition 5.3 final paragraph。
- 数学内容：P^{Bplus}_{n,k}=\tfrac12\det A^{Bplus}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：P；A。
- 关键步骤：T3.1.normalized；det D_J=2ζ；det C_I=ω。

#### P5.3.result

- 类型：statement；PDF 第 12 页；定位：Proposition 5.3 statement。
- 数学内容：等式 (1.5) 对 n,k\ge1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bplus。
- 关键步骤：P5.3.halfdet；AFFINE.multilinearity。
- 边界：不包含 k=0。

### L5.4

#### L5.4.a

- 类型：definition；PDF 第 12 页；定位：§5.3 definition display。
- 数学内容：a_j(m)=b_j(m)+b_j(m+1)，b_j、\Gamma_j 继承 (5.1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：a_j；b_j。

#### L5.4.c

- 类型：definition；PDF 第 12 页；定位：§5.3 definition display。
- 数学内容：c_j(m)=(-1)^m(a_j(m)+a_j(1-m))。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j。

#### L5.4.gamma

- 类型：definition；PDF 第 12 页；定位：§5.3 definition display。
- 数学内容：\gamma_j(m)=c_j(m)-tc_j(m-1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma。

#### L5.4.a.support

- 类型：proof_step；PDF 第 12 页；定位：after definition display。
- 数学内容：a_j 仅支撑在模 2k 的两个相邻剩余类 j、j-1。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：a_j；adjacent residues。
- 边界：k=1 时两类仍相邻且恰为全部模2类。

#### L5.4.c.symmetry

- 类型：proof_step；PDF 第 12 页；定位：after definition display。
- 数学内容：c_j(1-m)=-c_j(m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j。

#### L5.4.5.3

- 类型：statement；PDF 第 12 页；定位：(5.3)。
- 数学内容：c_j(m)=\Gamma_j(m)-\Gamma_j(m+1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：c_j；Gamma。
- 关键步骤：展开 a、c、Gamma 的定义。

#### L5.4.5.4

- 类型：statement；PDF 第 12 页；定位：(5.4)。
- 数学内容：\gamma_j(m)=(1+t)\Gamma_j(m)-\Gamma_j(m+1)-t\Gamma_j(m-1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma；Gamma。
- 关键步骤：L5.4.5.3；减去 t c_j(m-1)。

#### L5.4.5.5

- 类型：statement；PDF 第 12 页；定位：(5.5)。
- 数学内容：\gamma_j(m)=-t^{m-k-1}\gamma_j(2k+2-m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma。
- 关键步骤：L5.4.5.4；对 m、m+1、m-1 分别使用 L5.2.reflection；校准 t 因子。

#### L5.4.fixedcenter

- 类型：statement；PDF 第 12 页；定位：Lemma 5.4 in particular。
- 数学内容：\gamma_j(k+1)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma；fixed center。
- 关键步骤：m=k+1 代入 (5.5)；特征零中除以 2。

#### L5.4.reflection.expanded

- 类型：proof_step；PDF 第 12 页；定位：Lemma 5.4 proof display。
- 数学内容：T=2k+2，d=m-k-1 时，\gamma_j(m)=-t^d[(1+t)\Gamma_j(T-m)-t\Gamma_j(T-m-1)-\Gamma_j(T-m+1)]=-t^d\gamma_j(T-m)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：gamma；Gamma。
- 边界：移位项的 t 因子分别交换；不得逐项错误保留原位置。

### P5.5

#### P5.5.C

- 类型：definition；PDF 第 13 页；定位：Proposition 5.5 first sentence。
- 数学内容：C=C^B(a)，故 C_{p,j}=c_j(p)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C；a；c。

#### P5.5.firstcolumn

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 first display。
- 数学内容：([k+1]_B-t[k]_B)^TC_{\bullet,j}=\gamma_j(k+1)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bt；first column。
- 关键步骤：c 的有限 B 反射。

#### P5.5.restcolumns

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 first paragraph。
- 数学内容：r\ge2 时，(u^B_r-t\widetilde u^B_r)^TC_{\bullet,j}=\gamma_j(k+r)+t^{r-1}\gamma_j(k+2-r)=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bt；four terms。
- 关键步骤：L5.4.5.5 于 m=k+r。

#### P5.5.kernel

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 first paragraph。
- 数学内容：(V^{Bt})^TC=0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：V；C。
- 关键步骤：P5.5.firstcolumn；P5.5.restcolumns。

#### P5.5.CI.direct

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 complementary block first display。
- 数学内容：1≤p,j≤k 时，a_j(p)=\delta_{p,j}+\delta_{p,j-1}，仅 y=0 有贡献。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：a_j；C_I。

#### P5.5.CI.reflected

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 complementary block first display。
- 数学内容：1≤p,j≤k 时，a_j(1-p)=\delta_{p,1}\delta_{j,1}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：a_j；C_I。
- 关键步骤：两个同余要求 2ky=j+p-1 或 j+p-2；只有后者在 p=j=1、y=0 时可发生。
- 边界：原点重叠造成倍数 2，k=1 不能删去。

#### P5.5.CI.entries

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 complementary block second display。
- 数学内容：C_{p,j}=(-1)^p(\delta_{p,j}+\delta_{p,j-1}+\delta_{p,1}\delta_{j,1})，1≤p,j≤k。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P5.5.CI.bidiagonal

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 after block display。
- 数学内容：C_I 为上双对角块，对角为 -2,1,-1,1,\ldots。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。
- 边界：k=1 时 C_I=[-2]。

#### P5.5.CI.det

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 after block display。
- 数学内容：\det C_I=2\omega。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：C_I。

#### P5.5.DJ.undoubled

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 after block display。
- 数学内容：Bt 沿用 D^B，故 \det D^B_J=\zeta，没有额外倍数 2。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B_J。
- 关键步骤：L3.2.minor.B。

#### P5.5.pairing.m

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 pairing display first line。
- 数学内容：((D^B)^TC)_{ij}=\sum_m h_i(m)(b_j(m)+b_j(m+1))。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B；C。
- 关键步骤：L3.3.unfold.B；a 的定义。

#### P5.5.pairing.y

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 pairing display second line。
- 数学内容：((D^B)^TC)_{ij}=\sum_y(-1)^yt^{ky^2-(j-1)y}[h_i(j-2ky)+h_i(j-1-2ky)]。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B；C。
- 关键步骤：第一项 m=j-2ky；第二项 m+1=j-2ky。

#### P5.5.A

- 类型：definition；PDF 第 13 页；定位：Proposition 5.5 pairing display last line。
- 数学内容：A^{Bt}_{ij}=\sum_y(-1)^y t^{ky^2-(j-1)y}\widehat h_i(j-2ky)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A；hhat。

#### P5.5.pairing.hhat

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 pairing display last line。
- 数学内容：(D^B)^TC=A^{Bt}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：D^B；C；A。
- 关键步骤：P5.5.pairing.y；Bt.hhat.sum。

#### P5.5.halfdet

- 类型：proof_step；PDF 第 13 页；定位：Proposition 5.5 final paragraph。
- 数学内容：P^{Bt}_{n,k}=\tfrac12\det A^{Bt}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：P；A。
- 关键步骤：T3.1.normalized；det D_J=ζ；det C_I=2ω。

#### P5.5.result

- 类型：statement；PDF 第 13 页；定位：Proposition 5.5 statement。
- 数学内容：等式 (1.9) 对 n,k\ge1 成立。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Bt。
- 关键步骤：P5.5.halfdet；AFFINE.multilinearity。
- 边界：k=0 不在此证明范围。

### P6.1

#### P6.1.C0

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{C0}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；C0。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.Ct

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{Ct}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；Ct。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.BC

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{BC}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；BC。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.B0

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{B0}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；B0。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.Bminus

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{Bminus}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；Bminus。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.Bplus

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{Bplus}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；Bplus。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.Bt

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 first assertion。
- 数学内容：P^{Bt}_{n,0}=1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：empty rectangle；Bt。
- 关键步骤：WEYL.inversion.reduction 在 k=0 有效；有限 alternant/折叠给 nu(0) 倍比值；初始 basis 的上三角列变换；对角乘积等于 nu(0)。
- 边界：无需任意数值参数下所有 Pochhammer 因子非零。

#### P6.1.finite.ratio

- 类型：proof_step；PDF 第 13 页；定位：Proposition 6.1 proof display。
- 数学内容：\nu_\star(0)P^\star_{n,0}=\det(\Phi V^\star|_{k=0})/\Delta。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：P；V；nu。
- 关键步骤：k=0 的对称群约化；沿用 alternant 和行折叠计算。
- 边界：不使用互补核转移；不套用 det V_H=1。

#### P6.1.triangular

- 类型：proof_step；PDF 第 13 页；定位：Proposition 6.1 proof final lines。
- 数学内容：相对于定义 \Delta 的初始基，V^\star|_{k=0} 的列变换均为上三角。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：initial basis；V。

#### P6.1.diagonal.C0

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：C0 的列 r 对角系数为 1，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：C0；diagonal。

#### P6.1.product.C0

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：C0 的对角乘积为 1=\nu_{C0}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：C0；diagonal product；nu。

#### P6.1.diagonal.BC

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：BC 的列 r 对角系数为 1，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：BC；diagonal。

#### P6.1.product.BC

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：BC 的对角乘积为 1=\nu_{BC}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：BC；diagonal product；nu。

#### P6.1.diagonal.B0

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：B0 的列 r 对角系数为 1，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：B0；diagonal。

#### P6.1.product.B0

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：B0 的对角乘积为 1=\nu_{B0}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：B0；diagonal product；nu。

#### P6.1.diagonal.Ct

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：Ct 的列 r 对角系数为 1+t^r，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Ct；diagonal。

#### P6.1.product.Ct

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：Ct 的对角乘积为 (-t;t)_n=\nu_{Ct}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Ct；diagonal product；nu。

#### P6.1.diagonal.Bt

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：Bt 的列 r 对角系数为 1+t^r，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bt；diagonal。

#### P6.1.product.Bt

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：Bt 的对角乘积为 (-t;t)_n=\nu_{Bt}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bt；diagonal product；nu。

#### P6.1.diagonal.Bminus

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：Bminus 的列 r 对角系数为 1-\tau^{2r-1}，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bminus；diagonal。

#### P6.1.product.Bminus

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：Bminus 的对角乘积为 (\tau;\tau^2)_n=\nu_{Bminus}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bminus；diagonal product；nu。

#### P6.1.diagonal.Bplus

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table diagonal coefficient。
- 数学内容：Bplus 的列 r 对角系数为 1+t^{r-1}，1≤r≤n。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bplus；diagonal。

#### P6.1.product.Bplus

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 table product。
- 数学内容：Bplus 的对角乘积为 (-1;t)_n=\nu_{Bplus}(0)。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bplus；diagonal product；nu。

#### P6.1.Bt.firstcolumn

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 examples first display。
- 数学内容：Bt 在 k=0 的首列为 (1+t)\psi_1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bt。

#### P6.1.Bt.restcolumns

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 examples first display。
- 数学内容：Bt 在 k=0 的列 r≥2 为 (1+t^r)\psi_r-(t+t^{r-1})\psi_{r-1}。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bt。

#### P6.1.BC.firstcolumn

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 examples second display。
- 数学内容：BC 在 k=0 的首列为 \phi_1。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：BC。

#### P6.1.BC.restcolumns

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 examples second display。
- 数学内容：BC 在 k=0 的列 r≥2 为 \phi_r+(\tau-\tau^{2r-1})\phi_{r-1}-\tau^{2r-2}\phi_{r-2}。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：BC。
- 边界：r=2 时 phi_0=0。

#### P6.1.Bplus.center

- 类型：proof_step；PDF 第 14 页；定位：Proposition 6.1 example last paragraph。
- 数学内容：B_+ 首列是 C_0=2，相对 \chi_1=1 的对角为 1+t^0=2。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bplus；center。
- 边界：这是 nu_Bplus(0) 的首因子。

#### P6.1.extend.B0

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 consequently。
- 数学内容：无外部半因子的等式 (1.3) 在 k=0 时两边均为 1，故也成立。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：B0；J。
- 关键步骤：P6.1.B0；CONV.empty.det；CONV.empty.sum。
- 边界：Ct 的空向量属于偶和子格；不求值 K=0 的条目。

#### P6.1.extend.Bminus

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 consequently。
- 数学内容：无外部半因子的等式 (1.4) 在 k=0 时两边均为 1，故也成立。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Bminus；J。
- 关键步骤：P6.1.Bminus；CONV.empty.det；CONV.empty.sum。
- 边界：Ct 的空向量属于偶和子格；不求值 K=0 的条目。

#### P6.1.extend.C0

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 consequently。
- 数学内容：无外部半因子的等式 (1.6) 在 k=0 时两边均为 1，故也成立。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：C0；J。
- 关键步骤：P6.1.C0；CONV.empty.det；CONV.empty.sum。
- 边界：Ct 的空向量属于偶和子格；不求值 K=0 的条目。

#### P6.1.extend.Ct

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 consequently。
- 数学内容：无外部半因子的等式 (1.7) 在 k=0 时两边均为 1，故也成立。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：Ct；J。
- 关键步骤：P6.1.Ct；CONV.empty.det；CONV.empty.sum。
- 边界：Ct 的空向量属于偶和子格；不求值 K=0 的条目。

#### P6.1.extend.BC

- 类型：statement；PDF 第 13 页；定位：Proposition 6.1 consequently。
- 数学内容：无外部半因子的等式 (1.8) 在 k=0 时两边均为 1，故也成立。
- 假设：n\ge1，k=0；七种 case 的 Weyl-sum 定义、边界因子 nu(0)；等式首先在有理函数域中取消因子。
- 对象：BC；J。
- 关键步骤：P6.1.BC；CONV.empty.det；CONV.empty.sum。
- 边界：Ct 的空向量属于偶和子格；不求值 K=0 的条目。

### C6.2

#### C6.2.6.1

- 类型：statement；PDF 第 14 页；定位：(6.1)。
- 数学内容：\dfrac{\det[\phi_{k+r}(x_a)]}{\Delta_C(x)}=\det[\dot e_{n-i+j}-\dot e_{n+i+j}]。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：classical symplectic determinant。
- 关键步骤：有限列在 t=0 归为 [k+r]_C；C0 仿射式仅 y=0 留存。

#### C6.2.6.2.h

- 类型：statement；PDF 第 14 页；定位：(6.2) first equality。
- 数学内容：\dfrac{\det[\psi_{k+r}(x_a)]}{\Delta_B(x)}=\det[\dot e_{n-i+j}+\dot e_{n+i+j-1}]。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：classical B determinant。
- 关键步骤：B0 有限列特化；B0 仿射式仅 y=0 留存。

#### C6.2.6.2.hhat

- 类型：statement；PDF 第 14 页；定位：(6.2) second equality。
- 数学内容：\dfrac{\det[\psi_{k+r}(x_a)]}{\Delta_B(x)}=\tfrac12\det[\ddot e_{n-i+j}+\ddot e_{n+i+j-1}]。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：classical B doubled-coefficient determinant。
- 关键步骤：Bt 有限列特化；Bt 仿射式仅 y=0 留存。

#### C6.2.6.3

- 类型：statement；PDF 第 14 页；定位：(6.3)。
- 数学内容：\dfrac{\det[C_{k+r-1}(x_a)]}{\Delta_+(x)}=\tfrac12\det[\dot e_{n-i+j}+\dot e_{n+i+j-2}]。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：classical even-orthogonal determinant。
- 关键步骤：Bplus 有限列特化；Bplus 仿射式仅 y=0 留存。
- 边界：k≥1 保证第一列 C_k 对应 [k+1]_+ 的普通分支。

#### C6.2.columns.C0

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，C0 的每个有限列 v_r 化为 [k+r]_{C}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：C0；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.C0

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：C0 的有限表示在 t=0 时特化为 (6.1) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：C0；finite ratio。
- 关键步骤：C6.2.columns.C0；P2.2.ratio.C0。

#### C6.2.columns.Ct

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，Ct 的每个有限列 v_r 化为 [k+r]_{C}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Ct；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.Ct

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：Ct 的有限表示在 t=0 时特化为 (6.1) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Ct；finite ratio。
- 关键步骤：C6.2.columns.Ct；P2.2.ratio.Ct。

#### C6.2.columns.BC

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，BC 的每个有限列 v_r 化为 [k+r]_{C}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：BC；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.BC

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：BC 的有限表示在 t=0 时特化为 (6.1) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：BC；finite ratio。
- 关键步骤：C6.2.columns.BC；P2.2.ratio.BC。

#### C6.2.columns.B0

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，B0 的每个有限列 v_r 化为 [k+r]_{B}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：B0；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.B0

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：B0 的有限表示在 t=0 时特化为 (6.2) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：B0；finite ratio。
- 关键步骤：C6.2.columns.B0；P2.2.ratio.B0。

#### C6.2.columns.Bminus

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，Bminus 的每个有限列 v_r 化为 [k+r]_{B}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bminus；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.Bminus

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：Bminus 的有限表示在 t=0 时特化为 (6.2) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bminus；finite ratio。
- 关键步骤：C6.2.columns.Bminus；P2.2.ratio.Bminus。

#### C6.2.columns.Bt

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，Bt 的每个有限列 v_r 化为 [k+r]_{B}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bt；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.Bt

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：Bt 的有限表示在 t=0 时特化为 (6.2) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bt；finite ratio。
- 关键步骤：C6.2.columns.Bt；P2.2.ratio.Bt。

#### C6.2.columns.Bplus

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof first sentence。
- 数学内容：t=0（必要时 τ=0）时，Bplus 的每个有限列 v_r 化为 [k+r]_{+}。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bplus；V。
- 边界：r=1 单独定义的首列也需检验；r≥2 的 t^(r-1) 在 r≥2 时才消失。

#### C6.2.specialization.Bplus

- 类型：statement；PDF 第 14 页；定位：Corollary 6.2 after displayed identities。
- 数学内容：Bplus 的有限表示在 t=0 时特化为 (6.3) 对应的左侧有限 Weyl 比值。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bplus；finite ratio。
- 关键步骤：C6.2.columns.Bplus；P2.2.ratio.Bplus。

#### C6.2.nonzero.shift.C0

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof second sentence。
- 数学内容：C0 仿射公式中，每个非零 y 的参数指数严格为正，故 t=0 时每行只保留 y=0。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：C0；affine specialization。
- 关键步骤：相应 K,j 范围下的指数界。
- 边界：先使用已证明的有限多项式形式，避免负幂数值求值。

#### C6.2.nonzero.shift.B0

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof second sentence。
- 数学内容：B0 仿射公式中，每个非零 y 的参数指数严格为正，故 t=0 时每行只保留 y=0。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：B0；affine specialization。
- 关键步骤：相应 K,j 范围下的指数界。
- 边界：先使用已证明的有限多项式形式，避免负幂数值求值。

#### C6.2.nonzero.shift.Bplus

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof second sentence。
- 数学内容：Bplus 仿射公式中，每个非零 y 的参数指数严格为正，故 t=0 时每行只保留 y=0。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bplus；affine specialization。
- 关键步骤：相应 K,j 范围下的指数界。
- 边界：先使用已证明的有限多项式形式，避免负幂数值求值。

#### C6.2.nonzero.shift.Bt

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof second sentence。
- 数学内容：Bt 仿射公式中，每个非零 y 的参数指数严格为正，故 t=0 时每行只保留 y=0。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Bt；affine specialization。
- 关键步骤：相应 K,j 范围下的指数界。
- 边界：先使用已证明的有限多项式形式，避免负幂数值求值。

#### C6.2.Ct.exception

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof final sentences。
- 数学内容：Ct 在末列 j=k、位移 y=1 的权重指数 ky^2-jy=0，故不能逐项声称所有非零位移在 t=0 消失。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Ct；specialization exception。
- 边界：必须保留偶和子格和的整体结构。

#### C6.2.Ct.route

- 类型：proof_step；PDF 第 15 页；定位：Corollary 6.2 proof final sentences。
- 数学内容：Ct 应由其有限比值及已证奇偶投影恒等式，识别 t=0 的偶和子格和为同一辛行列式。
- 假设：n,k\ge1；1\le a,r\le n；1\le i,j\le k；继承 global Laurent 系数、分母及零延拓约定；t=0，平方根情形同时 \tau=0。
- 对象：Ct；classical determinant。
- 关键步骤：C6.2.specialization.Ct；P5.1.parity.det；P5.1.lastcolumn.zero。

### global

#### CONV.variables

- 类型：convention；PDF 第 1 页；定位：(1.1)前。
- 数学内容：x=(x_1,\ldots,x_n)，x_a 为可逆独立变量；n\ge1，矩形为 (k^n)，k 表宽度。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：n；k；x；(k^n)。

#### DEF.Edot

- 类型：definition；PDF 第 1 页；定位：(1.1)第一行。
- 数学内容：\dot E(u)=\prod_{a=1}^n(1+ux_a)(1+ux_a^{-1})=\sum_{r=0}^{2n}\dot e_r u^r。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\dot E；\dot e_r。

#### DEF.Eddot

- 类型：definition；PDF 第 1 页；定位：(1.1)第二行。
- 数学内容：\ddot E(u)=(1+u)\dot E(u)=\sum_{r=0}^{2n+1}\ddot e_r u^r。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\ddot E；\ddot e_r。

#### CONV.edot.zero

- 类型：convention；PDF 第 1 页；定位：(1.1)后。
- 数学内容：对所有整数 r\notin[0,2n]，\dot e_r=0。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\dot e。

#### CONV.eddot.zero

- 类型：convention；PDF 第 1 页；定位：(1.1)后。
- 数学内容：对所有整数 r\notin[0,2n+1]，\ddot e_r=0。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\ddot e。

#### COEFF.edot.palindrome

- 类型：statement；PDF 第 1 页；定位：(1.1)后第一式。
- 数学内容：对所有 r\in\mathbb Z，\dot e_{2n-r}=\dot e_r。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\dot e。

#### COEFF.eddot.palindrome

- 类型：statement；PDF 第 1 页；定位：(1.1)后第二式。
- 数学内容：对所有 r\in\mathbb Z，\ddot e_{2n+1-r}=\ddot e_r。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\ddot e。

#### COEFF.eddot.sum

- 类型：statement；PDF 第 1 页；定位：(1.1)后第三式。
- 数学内容：对所有 r\in\mathbb Z，\ddot e_r=\dot e_r+\dot e_{r-1}。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\ddot e；\dot e。

#### DEF.Lambda

- 类型：definition；PDF 第 1 页；定位：第1页末 row kernels。
- 数学内容：\Lambda_i(m)=\dot e_{n-i+m}-\dot e_{n+i+m}。
- 假设：n\ge1，k\ge0，1\le i\le k，m\in\mathbb Z；继承 global 零延拓。
- 对象：Lambda。

#### DEF.h

- 类型：definition；PDF 第 1 页；定位：第1页末 row kernels。
- 数学内容：h_i(m)=\dot e_{n-i+m}+\dot e_{n+i+m-1}。
- 假设：n\ge1，k\ge0，1\le i\le k，m\in\mathbb Z；继承 global 零延拓。
- 对象：h。

#### DEF.hplus

- 类型：definition；PDF 第 1 页；定位：第1页末 row kernels。
- 数学内容：h_i^+(m)=\dot e_{n-i+m}+\dot e_{n+i+m-2}。
- 假设：n\ge1，k\ge0，1\le i\le k，m\in\mathbb Z；继承 global 零延拓。
- 对象：hplus。

#### DEF.hhat

- 类型：definition；PDF 第 1 页；定位：第1页末 row kernels。
- 数学内容：\widehat h_i(m)=\ddot e_{n-i+m}+\ddot e_{n+i+m-1}。
- 假设：n\ge1，k\ge0，1\le i\le k，m\in\mathbb Z；继承 global 零延拓。
- 对象：hhat。

#### DEF.J

- 类型：definition；PDF 第 2 页；定位：(1.2)。
- 数学内容：\mathcal J_K[w,F;\mathcal L]=\sum_{(y_1,\ldots,y_k)\in\mathcal L}\det_{1\le i,j\le k}[w_j(y_i)F_i(j-Ky_i)]。
- 假设：\mathcal L\subseteq\mathbb Z^k；所用乘积有限支撑，或按已证明的有限行界解释。
- 对象：\mathcal J_K；w；F；\mathcal L。
- 边界：行变量是 y_i，列权重仍为 w_j；不得换为 w_i。。

#### CONV.weight.slot

- 类型：convention；PDF 第 2 页；定位：(1.2)后。
- 数学内容：\mathcal J 的权重槽中出现 j,y 的表达式表示 w_j(y)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：w。

#### DEF.even.lattice

- 类型：definition；PDF 第 2 页；定位：(1.2)后。
- 数学内容：\mathbb Z^k_{\mathrm{even}}=\{y\in\mathbb Z^k:\sum_{i=1}^k y_i\in2\mathbb Z\}。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\mathbb Z^k_{even}。

#### CONV.empty.det

- 类型：convention；PDF 第 2 页；定位：(1.2)后。
- 数学内容：空行列式取值 1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：det。
- 边界：k=0。

#### CONV.empty.sum

- 类型：convention；PDF 第 2 页；定位：(1.2)后。
- 数学内容：按空向量求和取值 1，且 k=0 时不求值任何矩阵元素或权重。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\mathcal J。
- 边界：不得以 K=0 的除法或权重公式求空矩阵元素。。

#### CONV.field.t

- 类型：convention；PDF 第 2 页；定位：Theorem A 前。
- 数学内容：除两个平方根情形外，系数域为 \mathbb Q(t,x_1,\ldots,x_n)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：coefficient field。

#### CONV.field.tau

- 类型：convention；PDF 第 2 页；定位：Theorem A 前。
- 数学内容：BC 与 B_- 两平方根情形系数域为 \mathbb Q(\tau,x_1,\ldots,x_n)，t=\tau^2，且 t^{r/2}:=\tau^r 对每个 r\in\mathbb Z。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：t；\tau。
- 边界：不是选择数值平方根，也不是任意域中的平方根公理。。

#### CONV.finite.sums

- 类型：convention；PDF 第 2 页；定位：(1.2)后。
- 数学内容：文中仿射求和因系数零延拓成为有限和。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：affine sums。
- 关键步骤：L3.3.row.support。

#### DEF.case.C0

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{C0}_{n,k} 表示 P^{C_n}_{(k^n)}(x;t,0)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；C0。

#### DEF.rho.C0

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{C0}(z)=(1-z^2)^{-1}。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；C0。

#### DEF.nu0.C0

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{C0}(0)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；C0。
- 边界：宽度零的边界归一化。

#### DEF.case.Ct

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{Ct}_{n,k} 表示 P^{C_n}_{(k^n)}(x;t,t)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；Ct。

#### DEF.rho.Ct

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{Ct}(z)=(1-tz^2)/(1-z^2)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；Ct。

#### DEF.nu0.Ct

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{Ct}(0)=(-t;t)_n。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；Ct。
- 边界：宽度零的边界归一化。

#### DEF.case.BC

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{BC}_{n,k} 表示 P^{BC_n}_{(k^n)}(x;\tau^2,-\tau,0)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；BC。

#### DEF.rho.BC

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{BC}(z)=(1+\tau z)/(1-z^2)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；BC。

#### DEF.nu0.BC

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{BC}(0)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；BC。
- 边界：宽度零的边界归一化。

#### DEF.case.B0

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{B0}_{n,k} 表示 P^{B_n}_{(k^n)}(x;t,0)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；B0。

#### DEF.rho.B0

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{B0}(z)=(1-z)^{-1}。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；B0。

#### DEF.nu0.B0

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{B0}(0)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；B0。
- 边界：宽度零的边界归一化。

#### DEF.case.Bminus

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{Bminus}_{n,k} 表示 P^{B_n}_{(k^n)}(x;\tau^2,-\tau)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；Bminus。

#### DEF.rho.Bminus

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{Bminus}(z)=(1+\tau z)/(1-z)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；Bminus。

#### DEF.nu0.Bminus

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{Bminus}(0)=(\tau;\tau^2)_n。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；Bminus。
- 边界：宽度零的边界归一化。

#### DEF.case.Bplus

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{Bplus}_{n,k} 表示 P^{B_n}_{(k^n)}(x;t,1)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；Bplus。

#### DEF.rho.Bplus

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{Bplus}(z)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；Bplus。

#### DEF.nu0.Bplus

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{Bplus}(0)=(-1;t)_n。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；Bplus。
- 边界：宽度零的边界归一化。

#### DEF.case.Bt

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：P^{Bt}_{n,k} 表示 P^{B_n}_{(k^n)}(x;t,t)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：P；Bt。

#### DEF.rho.Bt

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\rho_{Bt}(z)=(1-tz)/(1-z)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\rho；Bt。

#### DEF.nu0.Bt

- 类型：definition；PDF 第 3 页；定位：(2.1)后 case table。
- 数学内容：\nu_{Bt}(0)=(-t;t)_n。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu；Bt。
- 边界：宽度零的边界归一化。

#### DEF.pochhammer

- 类型：definition；PDF 第 3 页；定位：§2 first paragraph。
- 数学内容：(a;t)_m=\prod_{r=0}^{m-1}(1-at^r)，m\ge0。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Pochhammer。

#### DEF.Vn

- 类型：definition；PDF 第 3 页；定位：(2.1)前。
- 数学内容：V_n(t)=\prod_{r=1}^n(1+t+\cdots+t^{r-1})。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：V_n。

#### DEF.Wn

- 类型：definition；PDF 第 3 页；定位：(2.1)后。
- 数学内容：W_n=S_n\ltimes\{\pm1\}^n，作用为变量的置换和逆变换。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：W_n。

#### DEF.nu.positive

- 类型：definition；PDF 第 3 页；定位：(2.1)后。
- 数学内容：对每个七种 case，k\ge1 时 \nu_\star(k)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：\nu。
- 边界：不延伸为 k=0 的定义。

#### DEF.P.weylsum

- 类型：definition；PDF 第 3 页；定位：(2.1)。
- 数学内容：P^\star_{n,k}=\dfrac1{V_n(t)\nu_\star(k)}\sum_{w\in W_n}w\left[\prod_{a=1}^nx_a^{-k}\rho_\star(x_a)\prod_{a<b}\dfrac{(tx_a-x_b)(1-tx_ax_b)}{(x_a-x_b)(1-x_ax_b)}\right]。
- 假设：n\ge1，k\ge0；七种 rho、nu 数据；BC、B_- 中 t=τ²；等式首先在相应有理函数域中解释。
- 对象：P；W_n；\rho；\nu。
- 边界：包含 k=0；归一化因子先按有理函数取消。

#### SYMMETRIZER

- 类型：statement；PDF 第 3 页；定位：(2.1)后 symmetrizer identity。
- 数学内容：\sum_{\sigma\in S_n}\prod_{a<b}\dfrac{tz_{\sigma(a)}-z_{\sigma(b)}}{z_{\sigma(a)}-z_{\sigma(b)}}=V_n(t)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：symmetrizer；V_n。
- 关键步骤：反对称化；比较次数；SYMMETRIZER.recurrence。

#### SYMMETRIZER.recurrence

- 类型：proof_step；PDF 第 3 页；定位：symmetrizer identity 后。
- 数学内容：令 z_n=0 得 V_n(t)=(1+t+\cdots+t^{n-1})V_{n-1}(t)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：V_n。
- 边界：初值 V_0=1 由空乘积理解。

#### WEYL.symmetric.normalization

- 类型：convention；PDF 第 3 页；定位：case table 后。
- 数学内容：正宽矩形与空矩形的对称群归一化均为 V_n(t)，宽度零只改变边界 Pochhammer 因子。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：normalization。

#### WEYL.inversion.reduction

- 类型：statement；PDF 第 3 页；定位：(2.2)。
- 数学内容：P^\star_{n,k}=\dfrac1{\nu_\star(k)}\sum_{\eta\in\{\pm1\}^n}\prod_a u_a^{-k}\rho_\star(u_a)\prod_{a<b}\dfrac{1-tu_au_b}{1-u_au_b},\quad u_a=x_a^{\eta_a}。
- 假设：n\ge1，k\ge0；DEF.P.weylsum 与七种 case 数据。
- 对象：P；inversion sum。
- 关键步骤：SYMMETRIZER；其余因子的置换对称性。
- 边界：在 k=0 仍有效。

#### DEF.Nt

- 类型：definition；PDF 第 3 页；定位：§2.1 first line。
- 数学内容：N_t(z)=\prod_{a<b}(z_a-z_b)(1-tz_az_b)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：N_t。

#### DEF.fr.first

- 类型：definition；PDF 第 3 页；定位：§2.1。
- 数学内容：f_1(z)=z^{n-1}。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：f_1。
- 边界：第一列没有一般公式会给出的系数 2。。

#### DEF.fr.rest

- 类型：definition；PDF 第 3 页；定位：§2.1。
- 数学内容：f_r(z)=z^{n-r}+t^{r-1}z^{n+r-2},\quad2\le r\le n。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：f_r。

#### DEF.phi

- 类型：definition；PDF 第 4 页；定位：Lemma 2.1 后。
- 数学内容：\phi_m(z)=z^m-z^{-m}。
- 假设：m\in\mathbb Z，z 可逆。
- 对象：phi。

#### DEF.psi

- 类型：definition；PDF 第 4 页；定位：Lemma 2.1 后。
- 数学内容：\psi_m(z)=z^m-z^{1-m}。
- 假设：m\in\mathbb Z，z 可逆。
- 对象：psi。

#### DEF.C

- 类型：definition；PDF 第 4 页；定位：Lemma 2.1 后。
- 数学内容：C_m(z)=z^m+z^{-m}。
- 假设：m\in\mathbb Z，z 可逆。
- 对象：C。

#### DEF.L.basis

- 类型：definition；PDF 第 4 页；定位：finite foldings 前。
- 数学内容：L=n+k，e_1,\ldots,e_L 为标准基。
- 假设：n\ge1，k\ge0。
- 对象：L；e_p。

#### DEF.fold.C.positive

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[m]_C=e_m\ (m>0)。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[C]。

#### DEF.fold.C.zero

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[0]_C=0。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[C]。

#### DEF.fold.C.negative

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[m]_C=-e_{-m}\ (m<0)。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[C]。

#### DEF.fold.B.positive

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[m]_B=e_m\ (m\ge1)。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[B]。

#### DEF.fold.B.nonpositive

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[m]_B=-e_{1-m}\ (m\le0)。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[B]。

#### DEF.fold.plus.large

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[m]_+=e_m\ (m\ge2)。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[plus]。

#### DEF.fold.plus.center

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[1]_+=2e_1。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[plus]。
- 边界：C_0=2 强制中心系数为 2。。

#### DEF.fold.plus.nonpositive

- 类型：definition；PDF 第 4 页；定位：finite foldings cases。
- 数学内容：[m]_+=e_{2-m}\ (m\le0)。
- 假设：L=n+k；出现的非零折叠行须在 1,...,L 中。
- 对象：[plus]。

#### CONV.fold.range

- 类型：convention；PDF 第 4 页；定位：foldings 后。
- 数学内容：只使用折叠行属于 \{1,\ldots,L\} 的整数指标。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：folded rows。

#### DEF.Phi.C

- 类型：definition；PDF 第 4 页；定位：evaluation matrices。
- 数学内容：\Phi^C_{a,p}=\phi_p(x_a)。
- 假设：1\le a\le n，1\le p\le L。
- 对象：Phi。

#### DEF.Phi.B

- 类型：definition；PDF 第 4 页；定位：evaluation matrices。
- 数学内容：\Phi^B_{a,p}=\psi_p(x_a)。
- 假设：1\le a\le n，1\le p\le L。
- 对象：Phi。

#### DEF.Phi.plus.first

- 类型：definition；PDF 第 4 页；定位：evaluation matrices。
- 数学内容：\Phi^+_{a,1}=1。
- 假设：1\le a\le n，1\le p\le L。
- 对象：Phi。

#### DEF.Phi.plus.rest

- 类型：definition；PDF 第 4 页；定位：evaluation matrices。
- 数学内容：\Phi^+_{a,p}=C_{p-1}(x_a)\ (p\ge2)。
- 假设：1\le a\le n，1\le p\le L。
- 对象：Phi。

#### FOLD.eval.C

- 类型：statement；PDF 第 4 页；定位：evaluation matrices 后。
- 数学内容：\Phi^C[m]_C=\phi_m(x)（逐分量评估）。
- 假设：CONV.fold.range。
- 对象：Phi；bracket。
- 关键步骤：对应折叠分支；对应 Laurent 函数反射。

#### FOLD.eval.B

- 类型：statement；PDF 第 4 页；定位：evaluation matrices 后。
- 数学内容：\Phi^B[m]_B=\psi_m(x)（逐分量评估）。
- 假设：CONV.fold.range。
- 对象：Phi；bracket。
- 关键步骤：对应折叠分支；对应 Laurent 函数反射。

#### FOLD.eval.plus

- 类型：statement；PDF 第 4 页；定位：evaluation matrices 后。
- 数学内容：\Phi^+[m]_+=C_{m-1}(x)（逐分量评估）。
- 假设：CONV.fold.range。
- 对象：Phi；bracket。
- 关键步骤：对应折叠分支；对应 Laurent 函数反射。

#### DEF.chi.first

- 类型：definition；PDF 第 5 页；定位：(2.6)后。
- 数学内容：\chi_1(z)=1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：chi。

#### DEF.chi.rest

- 类型：definition；PDF 第 5 页；定位：(2.6)后。
- 数学内容：\chi_r(z)=C_{r-1}(z),\ r\ge2。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：chi。

#### WEYL.denominator.C

- 类型：statement；PDF 第 4 页；定位：(2.6)。
- 数学内容：\Delta_C(z)=\det[\phi_r(z_a)]=(-1)^n\prod_a z_a^{-n}(1-z_a^2)N_1(z)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Delta；Phi。
- 关键步骤：WEYL.denominator.monic.C。
- 边界：初始 n 列的 minor；均为非零有理函数。

#### WEYL.denominator.monic.C

- 类型：proof_step；PDF 第 5 页；定位：(2.6)后。
- 数学内容：\phi_r(z)/(z-z^{-1}) 是 z+z^{-1} 中次数 r-1 的首一多项式，故可用 Vandermonde 行列式求对应分母。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Vandermonde。

#### WEYL.denominator.inversion.C

- 类型：statement；PDF 第 5 页；定位：(2.6)后 last sentence。
- 数学内容：对某一行变量 z 作逆变换 z\mapsto z^{-1}，对应 C 分母乘以 -1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Delta；inversion。

#### WEYL.denominator.B

- 类型：statement；PDF 第 4 页；定位：(2.6)。
- 数学内容：\Delta_B(z)=\det[\psi_r(z_a)]=(-1)^n\prod_a z_a^{-(n-1)}(1-z_a)N_1(z)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Delta；Phi。
- 关键步骤：WEYL.denominator.monic.B。
- 边界：初始 n 列的 minor；均为非零有理函数。

#### WEYL.denominator.monic.B

- 类型：proof_step；PDF 第 5 页；定位：(2.6)后。
- 数学内容：\psi_r(z)/(z-1) 是 z+z^{-1} 中次数 r-1 的首一多项式，故可用 Vandermonde 行列式求对应分母。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Vandermonde。

#### WEYL.denominator.inversion.B

- 类型：statement；PDF 第 5 页；定位：(2.6)后 last sentence。
- 数学内容：对某一行变量 z 作逆变换 z\mapsto z^{-1}，对应 B 分母乘以 -z^{-1}。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Delta；inversion。

#### WEYL.denominator.plus

- 类型：statement；PDF 第 4 页；定位：(2.6)。
- 数学内容：\Delta_+(z)=\det[\chi_r(z_a)]=\prod_a z_a^{-(n-1)}N_1(z)。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Delta；Phi。
- 关键步骤：WEYL.denominator.monic.plus。
- 边界：初始 n 列的 minor；均为非零有理函数。

#### WEYL.denominator.monic.plus

- 类型：proof_step；PDF 第 5 页；定位：(2.6)后。
- 数学内容：\chi_r(z) 是 z+z^{-1} 中次数 r-1 的首一多项式，故可用 Vandermonde 行列式求对应分母。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Vandermonde。

#### WEYL.denominator.inversion.plus

- 类型：statement；PDF 第 5 页；定位：(2.6)后 last sentence。
- 数学内容：对某一行变量 z 作逆变换 z\mapsto z^{-1}，对应 plus 分母乘以 1。
- 假设：n\ge1；继承 global 的系数与零延拓约定。
- 对象：Delta；inversion。

#### DEF.u.C.first

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：u^{C}_1=[k+1]_{C}。
- 假设：n\ge1，k\ge0。
- 对象：u；bracket。

#### DEF.u.C.rest

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：u^{C}_r=[k+r]_{C}+t^{r-1}[k+2-r]_{C}\quad(r\ge2)。
- 假设：n\ge1，k\ge0，2\le r\le n。
- 对象：u；bracket。

#### DEF.u.B.first

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：u^{B}_1=[k+1]_{B}。
- 假设：n\ge1，k\ge0。
- 对象：u；bracket。

#### DEF.u.B.rest

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：u^{B}_r=[k+r]_{B}+t^{r-1}[k+2-r]_{B}\quad(r\ge2)。
- 假设：n\ge1，k\ge0，2\le r\le n。
- 对象：u；bracket。

#### DEF.u.+.first

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：u^{+}_1=[k+1]_{+}。
- 假设：n\ge1，k\ge0。
- 对象：u；bracket。

#### DEF.u.+.rest

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：u^{+}_r=[k+r]_{+}+t^{r-1}[k+2-r]_{+}\quad(r\ge2)。
- 假设：n\ge1，k\ge0，2\le r\le n。
- 对象：u；bracket。

#### DEF.utilde.C.first

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：\widetilde u^{C}_1=[k]_{C}。
- 假设：n\ge1，k\ge0。
- 对象：utilde；bracket。

#### DEF.utilde.C.rest

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：\widetilde u^{C}_r=[k+r-1]_{C}+t^{r-1}[k+1-r]_{C}\quad(r\ge2)。
- 假设：n\ge1，k\ge0，2\le r\le n。
- 对象：utilde；bracket。

#### DEF.utilde.B.first

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：\widetilde u^{B}_1=[k]_{B}。
- 假设：n\ge1，k\ge0。
- 对象：utilde；bracket。

#### DEF.utilde.B.rest

- 类型：definition；PDF 第 5 页；定位：§2.2 first display。
- 数学内容：\widetilde u^{B}_r=[k+r-1]_{B}+t^{r-1}[k+1-r]_{B}\quad(r\ge2)。
- 假设：n\ge1，k\ge0，2\le r\le n。
- 对象：utilde；bracket。

#### DEF.V.C0

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{C0}=(v_1,\ldots,v_n)，v_r=u^C_r；对应评估矩阵为 \Phi^C，分母为 \Delta_C。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；C0；Phi；Delta。

#### DEF.V.Ct

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{Ct}=(v_1,\ldots,v_n)，v_r=[k+r]_C-t^r[k-r]_C；对应评估矩阵为 \Phi^C，分母为 \Delta_C。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；Ct；Phi；Delta。

#### DEF.V.BC

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{BC}=(v_1,\ldots,v_n)，v_r=u^C_r+\tau\widetilde u^C_r；对应评估矩阵为 \Phi^C，分母为 \Delta_C。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；BC；Phi；Delta。

#### DEF.V.B0

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{B0}=(v_1,\ldots,v_n)，v_r=u^B_r；对应评估矩阵为 \Phi^B，分母为 \Delta_B。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；B0；Phi；Delta。

#### DEF.V.Bminus

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{Bminus}=(v_1,\ldots,v_n)，v_r=[k+r]_B+\tau^{2r-1}[k+1-r]_B；对应评估矩阵为 \Phi^B，分母为 \Delta_B。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；Bminus；Phi；Delta。

#### DEF.V.Bplus

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{Bplus}=(v_1,\ldots,v_n)，v_r=u^+_r；对应评估矩阵为 \Phi^+，分母为 \Delta_+。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；Bplus；Phi；Delta。

#### DEF.V.Bt

- 类型：definition；PDF 第 5 页；定位：Table 1。
- 数学内容：V^{Bt}=(v_1,\ldots,v_n)，v_r=u^B_r-t\widetilde u^B_r；对应评估矩阵为 \Phi^B，分母为 \Delta_B。
- 假设：n\ge1，k\ge0；BC、B_- 中 t=τ²；对应 bracket 定义。
- 对象：V；Bt；Phi；Delta。

#### CONV.sections3to5

- 类型：convention；PDF 第 6 页；定位：§3 first paragraph。
- 数学内容：第3--5节一律假设 n,k\ge1，L=n+k。
- 对象：n；k；L。
- 边界：k=0 不在互补核转移证明域内。

#### DEF.Q0

- 类型：definition；PDF 第 6 页；定位：§3 first display。
- 数学内容：Q_0=\{1,\ldots,n\}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：Q0。

#### DEF.index.J

- 类型：definition；PDF 第 6 页；定位：§3 first display。
- 数学内容：J=\{n+1,\ldots,n+k\}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：J。

#### DEF.H

- 类型：definition；PDF 第 6 页；定位：§3 first display。
- 数学内容：H=\{k+1,\ldots,k+n\}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：H。

#### DEF.I

- 类型：definition；PDF 第 6 页；定位：§3 first display。
- 数学内容：I=\{1,\ldots,k\}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：I。

#### DEF.omega

- 类型：definition；PDF 第 6 页；定位：§3 first display。
- 数学内容：\omega=(-1)^{k(k+1)/2}。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：omega。

#### DEF.zeta

- 类型：definition；PDF 第 6 页；定位：§3 first display。
- 数学内容：\zeta=(-1)^{nk}\omega。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：zeta。

#### CONV.subset.order

- 类型：convention；PDF 第 6 页；定位：§3 after first display。
- 数学内容：所有子集总按递增顺序排列。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：subsets。
- 边界：minor 符号依赖该顺序。

#### CONV.minor.columns

- 类型：convention；PDF 第 6 页；定位：§3 after first display。
- 数学内容：n\times L 矩阵的下标子集选择列。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：X_Q；Phi_Q。

#### CONV.minor.rows

- 类型：convention；PDF 第 6 页；定位：§3 after first display。
- 数学内容：有 L 行的矩阵的下标子集选择行。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：U_J；V_H；C_I。

#### AFFINE.row.support

- 类型：statement；PDF 第 8 页；定位：Lemma 3.3 后 common bound。
- 数学内容：若 K>0，\mathcal E_r=0 对 r\notin[0,N]，\delta\in\{0,1,2\}，则整行 [\mathcal E_{n-i+j-Ky}+\sigma\mathcal E_{n+i+j-Ky-\delta}]_{j=1}^k 为零，除非 \left\lceil\frac{n-i+1-N}{K}\right\rceil\le y\le\left\lfloor\frac{n+i+k-\delta}{K}\right\rfloor。
- 假设：n,k\ge1，1\le i\le k，K>0，N\ge0；\mathcal E 的上述零延拓；\delta\in\{0,1,2\}；\sigma 任意标量。
- 对象：finite row support。
- 关键步骤：2i-δ≥0；y 在下界外使所有下标>N；y 在上界外使所有下标<0。
- 边界：行界统一控制所有列 j；不是单个元素的最小支撑区间。

#### AFFINE.row.support.edot

- 类型：proof_step；PDF 第 8 页；定位：common bound 后。
- 数学内容：对 \Lambda,h,h^+ 使用 N=2n；对 \widehat h 使用 N=2n+1。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：finite support。

#### AFFINE.multilinearity

- 类型：statement；PDF 第 8 页；定位：common bound 后。
- 数学内容：A_{ij}=\sum_yw_j(y)F_i(j-Ky) 时，由有限行多线性，\det A=\mathcal J_K[w,F;\mathbb Z^k]。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：A；J。
- 关键步骤：AFFINE.row.support；逐行展开行列式。
- 边界：不直接声称偶子格和等于单个无符号行和行列式。

#### AFFINE.exponent.nonnegative

- 类型：statement；PDF 第 8 页；定位：§3.3 last paragraph。
- 数学内容：所有权重的参数指数均形如 E(y)=\frac K2y^2-(j-\eta)y；其中 \eta\in\{0,\tfrac12,1\}，K/2\ge k-\eta，j-\eta\ge0。对每个整数 y，E(y)\ge0。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：parameter exponent。
- 关键步骤：j≤k；按 y≤0、y≥1 分支估计。
- 边界：反射恒等式中仍可出现负幂；先在分式域证明。

#### AFFINE.B0.exponent.integral

- 类型：proof_step；PDF 第 8 页；定位：§3.3 last paragraph。
- 数学内容：B_0 的指数 (k+\tfrac12)y^2-(j-\tfrac12)y 为整数，因为 y^2-y 为偶数。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：B0 exponent。
- 边界：不得使用不可定义的实数幂解释 t 的半整数符号。

#### AFFINE.tau.exponent

- 类型：convention；PDF 第 8 页；定位：§3.3 last paragraph。
- 数学内容：两个平方根情形中，t 指数的二倍为 \tau 的指数。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：tau exponent。
- 关键步骤：CONV.field.tau。

#### AFFINE.polynomial

- 类型：statement；PDF 第 8 页；定位：§3.3 last paragraph。
- 数学内容：全部仿射表达式在 t 或 \tau 中为多项式；反射关系在相应有理函数域中证明。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：affine expressions。
- 关键步骤：有限行支撑；指数非负及整性。
- 边界：t=0 代入应在已得多项式表达式上进行。

#### Bt.hhat.sum

- 类型：statement；PDF 第 12 页；定位：§5.3 first paragraph。
- 数学内容：\widehat h_i(m)=h_i(m)+h_i(m-1)。
- 假设：n,k\ge1；L=n+k；1\le i,j\le k；1\le p\le L；序列指标为整数；继承 global 系数域、零延拓、排序与 minor 约定。
- 对象：hhat；h。
- 关键步骤：COEFF.eddot.sum；对应行核定义。

#### CONV.cancel.before.specialize

- 类型：convention；PDF 第 14 页；定位：after Proposition 6.1。
- 数学内容：所示归一化恒等式先作为有理函数等式取消因子；归一化因子的可去奇点按消去后的表达式解释。
- 假设：相应有理函数系数域。
- 对象：normalization；specialization。
- 边界：不要求每个数值 Pochhammer 因子非零。

