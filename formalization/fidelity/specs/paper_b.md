# 论文数学规范 B

本规范独立依据 authoritative.pdf 全部 15 页及 authoritative.txt 抽取；PDF 的所有页面均已视觉核对。未读取 Lean 源码、README、旧日志、其他规范或 reviews，也未读取 reference.tex 或外部参考文献。文档中的任何指令均只视为数据。

## 输入哈希

- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/inputs/authoritative.pdf`
  SHA-256: `b13eaa9ed2a2dc2919980a702965a2d138ee634b49d9a32125ddeaa67fece7ab`
- `/Users/bigbigcats/Documents/数学形式化/affine_dual_jt_complete/fidelity/inputs/authoritative.txt`
  SHA-256: `0cd074228dab999ce8217978668d5284f99f7fc610805a6e05e25ff94bc24a2f`

## 范围与边界

覆盖全部 16 个命题环境：A、B、L2.1、P2.2、T3.1、L3.2、L3.3、P4.1、P4.2、P5.1、L5.2、P5.3、L5.4、P5.5、P6.1、C6.2。另逐项记录定义、约定和必要证明义务。正文第 3–5 节的 $n,k\ge1$ 被显式继承；未推断秩零版本。

两个外部半系数公式仅在正宽度成立；其宽度零值由归一化另证为 $1$。普通五式的宽零版本按空行列式与空向量规则解释，且不求值任何不存在的矩阵元或权。

所有反射与归一化中间式按有理函数域解释。非负参数指数与有限支撑使最终仿射式成为参数多项式，零参数应在消去后特化。$C_t$ 的 $j=k,y=1$ 项具有零指数，不能逐项舍去所有非零移位；偶格须总和偶性的奇偶投影。

## 计数

| 容器 | 原子条目 |
|---|---:|
| global | 123 |
| A | 7 |
| B | 2 |
| L2.1 | 10 |
| P2.2 | 16 |
| T3.1 | 9 |
| L3.2 | 21 |
| L3.3 | 6 |
| P4.1 | 22 |
| P4.2 | 21 |
| P5.1 | 20 |
| L5.2 | 8 |
| P5.3 | 13 |
| L5.4 | 6 |
| P5.5 | 15 |
| P6.1 | 24 |
| C6.2 | 18 |
| 合计 | 341 |

## 全部原子规范

### global

#### DEF.Edot

- 类型：`definition`；页码：1；定位：(1.1), first generating polynomial

**规范**：$\dot E(u)=\prod_{a=1}^{n}(1+ux_a)(1+ux_a^{-1})=\sum_{r=0}^{2n}\dot e_r u^r$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：dotE；dot_e

#### DEF.Eddot

- 类型：`definition`；页码：1；定位：(1.1), second generating polynomial

**规范**：$\ddot E(u)=(1+u)\dot E(u)=\sum_{r=0}^{2n+1}\ddot e_r u^r$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：ddotE；ddot_e

**证明路线 / 依赖**：DEF.Edot

#### CONV.dot.zero

- 类型：`convention`；页码：1；定位：paragraph below (1.1)

**规范**：$r\in\mathbb Z\setminus[0,2n]\Longrightarrow\dot e_r=0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：dot_e

**边界与核查义务**：特别包括所有负指标；原文没有把负指标截成 0 后再取系数。

#### CONV.ddot.zero

- 类型：`convention`；页码：1；定位：paragraph below (1.1)

**规范**：$r\in\mathbb Z\setminus[0,2n+1]\Longrightarrow\ddot e_r=0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：ddot_e

#### COEFF.dot.palindrome

- 类型：`statement`；页码：1；定位：three equations below (1.1), first

**规范**：对每个 $r\in\mathbb Z$，$\dot e_{2n-r}=\dot e_r$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：dot_e

**证明路线 / 依赖**：DEF.Edot；CONV.dot.zero

#### COEFF.ddot.palindrome

- 类型：`statement`；页码：1；定位：three equations below (1.1), second

**规范**：对每个 $r\in\mathbb Z$，$\ddot e_{2n+1-r}=\ddot e_r$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：ddot_e

**证明路线 / 依赖**：DEF.Eddot；CONV.ddot.zero

#### COEFF.convolution

- 类型：`statement`；页码：1；定位：three equations below (1.1), third

**规范**：对每个 $r\in\mathbb Z$，$\ddot e_r=\dot e_r+\dot e_{r-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：dot_e；ddot_e

**证明路线 / 依赖**：DEF.Eddot；CONV.dot.zero；CONV.ddot.zero

#### COEFF.endpoints

- 类型：`proof_step`；页码：1；定位：(1.1), constant and leading coefficients

**规范**：$\dot e_0=\dot e_{2n}=1$ 且 $\ddot e_0=\ddot e_{2n+1}=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：dot_e；ddot_e

**证明路线 / 依赖**：DEF.Edot；DEF.Eddot

#### DEF.Lambda

- 类型：`definition`；页码：1；定位：row kernels at foot of page

**规范**：$\Lambda_i(m)=\dot e_{n-i+m}-\dot e_{n+i+m}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$m\in\mathbb Z$

**对象**：Lambda

**证明路线 / 依赖**：DEF.Edot；DEF.Eddot；CONV.dot.zero；CONV.ddot.zero

#### DEF.h

- 类型：`definition`；页码：1；定位：row kernels at foot of page

**规范**：$h_i(m)=\dot e_{n-i+m}+\dot e_{n+i+m-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$m\in\mathbb Z$

**对象**：h

**证明路线 / 依赖**：DEF.Edot；DEF.Eddot；CONV.dot.zero；CONV.ddot.zero

#### DEF.hplus

- 类型：`definition`；页码：1；定位：row kernels at foot of page

**规范**：$h_i^+(m)=\dot e_{n-i+m}+\dot e_{n+i+m-2}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$m\in\mathbb Z$

**对象**：hplus

**证明路线 / 依赖**：DEF.Edot；DEF.Eddot；CONV.dot.zero；CONV.ddot.zero

#### DEF.hhat

- 类型：`definition`；页码：1；定位：row kernels at foot of page

**规范**：$\widehat h_i(m)=\ddot e_{n-i+m}+\ddot e_{n+i+m-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$m\in\mathbb Z$

**对象**：hhat

**证明路线 / 依赖**：DEF.Edot；DEF.Eddot；CONV.dot.zero；CONV.ddot.zero

#### DEF.J

- 类型：`definition`；页码：2；定位：(1.2)

**规范**：$\mathcal J_K[w,F;\mathcal L]=\sum_{(y_1,\ldots,y_k)\in\mathcal L}\det_{1\le i,j\le k}[w_j(y_i)F_i(j-Ky_i)]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$\mathcal L\subseteq\mathbb Z^k$；$w_j$ 是列指标 $j$ 与移位 $y$ 的权；$F_i$ 是行核

**对象**：J_K

**边界与核查义务**：同一个向量分量 $y_i$ 用于整行；不能改成每列独立的 $y_j$。；一般序列的无限和须另有有限支撑解释；论文实际使用的核由零延拓保证有限。

#### CONV.weight.slot

- 类型：`convention`；页码：2；定位：text after (1.2)

**规范**：权槽中的含 $j,y$ 的式子表示 $w_j(y)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：J_K；w_j

#### DEF.even.lattice

- 类型：`definition`；页码：2；定位：text after (1.2)

**规范**：$\mathbb Z^k_{\rm even}=\{y\in\mathbb Z^k:\sum_{i=1}^{k}y_i\in2\mathbb Z\}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Z_even

#### CONV.empty.det

- 类型：`convention`；页码：2；定位：empty-object conventions

**规范**：$0\times0$ 空行列式的值为 $1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：det

**边界与核查义务**：外部的 $1/2$ 仍然保留，不能由此得到带半系数公式的正确宽零值。

#### CONV.empty.vector

- 类型：`convention`；页码：2；定位：empty-object conventions

**规范**：空向量指标的和取值 $1$；$\mathbb Z^0$ 及其偶格的唯一空向量均贡献空行列式。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：J_K；Z_even

#### CONV.empty.noeval

- 类型：`convention`；页码：2；定位：sentence beginning When k = 0

**规范**：$k=0$ 时 (1.2) 不求值任何矩阵元或权。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：J_K

**边界与核查义务**：此时即使 $K=2k=0$，也不能要求正宽度所用 $K>0$ 或求值不存在的列权。

#### CONV.coefficient.field

- 类型：`convention`；页码：2；定位：coefficient field paragraph

**规范**：在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：coefficient_field

**边界与核查义务**：$t$ 或 $\tau$ 在反射证明中为形式参数，不能直接将负指数反射式代入零。

#### CONV.sqrt

- 类型：`convention`；页码：2；定位：coefficient field paragraph

**规范**：在平方根两例中，对每个 $r\in\mathbb Z$ 约定 $t^{r/2}:=\tau^r$，且 $t=\tau^2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：t；tau

**边界与核查义务**：包括负的 $r$；这是有理函数域语义，不是选择数值平方根。

#### DEF.case.labels

- 类型：`definition`；页码：3；定位：Section 2 opening paragraph

**规范**：$P^\star_{n,k}$ 依次用 $\star=C_0,C_t,BC,B_0,B_-,B_+,B_t$ 表示 (1.6),(1.7),(1.8),(1.3),(1.4),(1.5),(1.9) 中的七种多项式。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_star

#### DEF.Pochhammer

- 类型：`definition`；页码：3；定位：Section 2 opening paragraph

**规范**：$(a;t)_m=\prod_{r=0}^{m-1}(1-at^r)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\ge0$

**对象**：Pochhammer

**边界与核查义务**：空积为 $1$。

#### DEF.Vn

- 类型：`definition`；页码：3；定位：display preceding (2.1)

**规范**：$V_n(t)=\prod_{r=1}^{n}(1+t+\cdots+t^{r-1})$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_n

#### DEF.Wn

- 类型：`definition`；页码：3；定位：sentence after (2.1)

**规范**：$W_n=S_n\ltimes\{\pm1\}^n$，通过置换变量和分别取逆作用。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：W_n

#### DEF.Weyl.sum

- 类型：`definition`；页码：3；定位：(2.1)

**规范**：$P^\star_{n,k}=\dfrac{1}{V_n(t)\nu_\star(k)}\sum_{w\in W_n}w\!\left[\prod_{a=1}^{n}x_a^{-k}\rho_\star(x_a)\prod_{a<b}\dfrac{(tx_a-x_b)(1-tx_ax_b)}{(x_a-x_b)(1-x_ax_b)}\right]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$

**对象**：P_star；rho_star；nu_star；V_n；W_n

**证明路线 / 依赖**：DEF.Vn；DEF.Wn

**边界与核查义务**：包括宽度零；先作为有理函数恒等式解释。

#### DEF.nu.positive

- 类型：`definition`；页码：3；定位：sentence after (2.1)

**规范**：所有七例在 $k\ge1$ 时均有 $\nu_\star(k)=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge1$

**对象**：nu_star

#### DEF.rho.C0

- 类型：`definition`；页码：3；定位：table after (2.1), C0 row

**规范**：$\rho_{C_0}(z)=(1-z^2)^{-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：rho_C0

#### DEF.nu.zero.C0

- 类型：`definition`；页码：3；定位：table after (2.1), C0 row

**规范**：$\nu_{C_0}(0)=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：nu_C0

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### DEF.rho.Ct

- 类型：`definition`；页码：3；定位：table after (2.1), Ct row

**规范**：$\rho_{C_t}(z)=(1-tz^2)/(1-z^2)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：rho_Ct

#### DEF.nu.zero.Ct

- 类型：`definition`；页码：3；定位：table after (2.1), Ct row

**规范**：$\nu_{C_t}(0)=(-t;t)_n$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：nu_Ct

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### DEF.rho.BC

- 类型：`definition`；页码：3；定位：table after (2.1), BC row

**规范**：$\rho_{BC}(z)=(1+\tau z)/(1-z^2)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$t=\tau^2$

**对象**：rho_BC

#### DEF.nu.zero.BC

- 类型：`definition`；页码：3；定位：table after (2.1), BC row

**规范**：$\nu_{BC}(0)=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$t=\tau^2$

**对象**：nu_BC

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### DEF.rho.B0

- 类型：`definition`；页码：3；定位：table after (2.1), B0 row

**规范**：$\rho_{B_0}(z)=(1-z)^{-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：rho_B0

#### DEF.nu.zero.B0

- 类型：`definition`；页码：3；定位：table after (2.1), B0 row

**规范**：$\nu_{B_0}(0)=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：nu_B0

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### DEF.rho.Bminus

- 类型：`definition`；页码：3；定位：table after (2.1), Bminus row

**规范**：$\rho_{B_-}(z)=(1+\tau z)/(1-z)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$t=\tau^2$

**对象**：rho_Bminus

#### DEF.nu.zero.Bminus

- 类型：`definition`；页码：3；定位：table after (2.1), Bminus row

**规范**：$\nu_{B_-}(0)=(\tau;\tau^2)_n$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$t=\tau^2$

**对象**：nu_Bminus

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### DEF.rho.Bplus

- 类型：`definition`；页码：3；定位：table after (2.1), Bplus row

**规范**：$\rho_{B_+}(z)=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：rho_Bplus

#### DEF.nu.zero.Bplus

- 类型：`definition`；页码：3；定位：table after (2.1), Bplus row

**规范**：$\nu_{B_+}(0)=(-1;t)_n$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：nu_Bplus

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### DEF.rho.Bt

- 类型：`definition`；页码：3；定位：table after (2.1), Bt row

**规范**：$\rho_{B_t}(z)=(1-tz)/(1-z)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：rho_Bt

#### DEF.nu.zero.Bt

- 类型：`definition`；页码：3；定位：table after (2.1), Bt row

**规范**：$\nu_{B_t}(0)=(-t;t)_n$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：nu_Bt

**边界与核查义务**：不以该因子的某个数值非零为额外结论前提；在有理函数域消去后特化。

#### WEYL.symmetrizer

- 类型：`proof_step`；页码：3；定位：standard symmetrizer identity

**规范**：$\sum_{\sigma\in S_n}\prod_{a<b}\dfrac{t z_{\sigma(a)}-z_{\sigma(b)}}{z_{\sigma(a)}-z_{\sigma(b)}}=V_n(t)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：S_n；V_n

**证明路线 / 依赖**：DEF.Vn

**边界与核查义务**：变量取相同数值的分母问题按有理函数恒等式消去处理。

#### WEYL.symmetrizer.recurrence

- 类型：`proof_step`；页码：3；定位：paragraph after symmetrizer

**规范**：由交错化及次数比较证明对称化恒等式；令 $z_n=0$ 得 $V_n=(1+t+\cdots+t^{n-1})V_{n-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_n

**证明路线 / 依赖**：WEYL.symmetrizer

#### WEYL.inversion.sum

- 类型：`proof_step`；页码：3；定位：(2.2)

**规范**：$P^\star_{n,k}=\nu_\star(k)^{-1}\sum_{\eta\in\{\pm1\}^n}\prod_a u_a^{-k}\rho_\star(u_a)\prod_{a<b}\dfrac{1-tu_au_b}{1-u_au_b}$，其中 $u_a=x_a^{\eta_a}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$

**对象**：P_star；u_a

**证明路线 / 依赖**：DEF.Weyl.sum；WEYL.symmetrizer

**边界与核查义务**：宽度零仍有效。

#### DEF.Nt

- 类型：`definition`；页码：3；定位：Section 2.1 first sentence

**规范**：$N_t(z)=\prod_{a<b}(z_a-z_b)(1-tz_az_b)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：N_t

#### DEF.fr.first

- 类型：`definition`；页码：3；定位：Section 2.1 first display

**规范**：$f_1(z)=z^{n-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：f_1

**边界与核查义务**：第一列不套用 $r\ge2$ 的双项式，避免重复一份。

#### DEF.fr.rest

- 类型：`definition`；页码：3；定位：Section 2.1 first display

**规范**：$f_r(z)=z^{n-r}+t^{r-1}z^{n+r-2}$，$2\le r\le n$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：f_r

#### DEF.phi

- 类型：`definition`；页码：4；定位：paragraph after Lemma 2.1

**规范**：$\phi_m(z)=z^m-z^{-m}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：phi

#### DEF.psi

- 类型：`definition`；页码：4；定位：paragraph after Lemma 2.1

**规范**：$\psi_m(z)=z^m-z^{1-m}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：psi

#### DEF.Cfun

- 类型：`definition`；页码：4；定位：paragraph after Lemma 2.1

**规范**：$C_m(z)=z^m+z^{-m}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：Cfun

#### DEF.L

- 类型：`definition`；页码：4；定位：folding paragraph

**规范**：$L=n+k$，$e_1,\ldots,e_L$ 是标准基。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$

**对象**：L；standard_basis

#### DEF.fold.C.positive

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[m]_C=e_m$，$m>0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_C

**证明路线 / 依赖**：DEF.L

#### DEF.fold.C.zero

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[0]_C=0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_C

**证明路线 / 依赖**：DEF.L

#### DEF.fold.C.negative

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[m]_C=-e_{-m}$，$m<0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_C

**证明路线 / 依赖**：DEF.L

#### DEF.fold.B.positive

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[m]_B=e_m$，$m\ge1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_B

**证明路线 / 依赖**：DEF.L

#### DEF.fold.B.nonpositive

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[m]_B=-e_{1-m}$，$m\le0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_B

**证明路线 / 依赖**：DEF.L

#### DEF.fold.plus.high

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[m]_+=e_m$，$m\ge2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_plus

**证明路线 / 依赖**：DEF.L

#### DEF.fold.plus.center

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[1]_+=2e_1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_plus

**证明路线 / 依赖**：DEF.L

**边界与核查义务**：$[1]_+$ 的系数 $2$ 必须保留。

#### DEF.fold.plus.nonpositive

- 类型：`definition`；页码：4；定位：finite folding cases

**规范**：$[m]_+=e_{2-m}$，$m\le0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；折叠后的基指标属于 $\{1,\ldots,L\}$；仅使用满足该条件的指标

**对象**：fold_plus

**证明路线 / 依赖**：DEF.L

#### CONV.fold.range

- 类型：`convention`；页码：4；定位：sentence after foldings

**规范**：只出现折叠行属于 $\{1,\ldots,L\}$ 的整数指标。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：fold_C；fold_B；fold_plus

#### DEF.Phi.C

- 类型：`definition`；页码：4；定位：evaluation matrices display

**规范**：$\Phi^C_{a,p}=\phi_p(x_a)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a\le n$；$1\le p\le L$

**对象**：Phi_C

#### DEF.Phi.B

- 类型：`definition`；页码：4；定位：evaluation matrices display

**规范**：$\Phi^B_{a,p}=\psi_p(x_a)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a\le n$；$1\le p\le L$

**对象**：Phi_B

#### DEF.Phi.plus.first

- 类型：`definition`；页码：4；定位：evaluation matrices display

**规范**：$\Phi^+_{a,1}=1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a\le n$；$1\le p\le L$

**对象**：Phi_plus

#### DEF.Phi.plus.rest

- 类型：`definition`；页码：4；定位：evaluation matrices display

**规范**：$\Phi^+_{a,p}=C_{p-1}(x_a)$，$p\ge2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a\le n$；$1\le p\le L$

**对象**：Phi_plus

#### EVAL.fold.C

- 类型：`statement`；页码：4；定位：sentence beginning Thus

**规范**：$\Phi^C[m]_C=\phi_m(x)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；允许范围内的 $m\in\mathbb Z$；逐变量向量求值

**对象**：Phi_C；fold_C

#### EVAL.fold.B

- 类型：`statement`；页码：4；定位：sentence beginning Thus

**规范**：$\Phi^B[m]_B=\psi_m(x)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；允许范围内的 $m\in\mathbb Z$；逐变量向量求值

**对象**：Phi_B；fold_B

#### EVAL.fold.plus

- 类型：`statement`；页码：4；定位：sentence beginning Thus

**规范**：$\Phi^+[m]_+=C_{m-1}(x)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；允许范围内的 $m\in\mathbb Z$；逐变量向量求值

**对象**：Phi_plus；fold_plus

**边界与核查义务**：特别 $m=1$ 时 $C_0=2$，而 $\Phi^+_{a,1}=1$。

#### DEF.chi

- 类型：`definition`；页码：5；定位：first sentence

**规范**：$\chi_1=1$，$\chi_r=C_{r-1}$（$r\ge2$）。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：chi

#### WEYL.delta.C

- 类型：`statement`；页码：4；定位：(2.6), C

**规范**：$\Delta_C(z)=\det_{a,r}[\phi_r(z_a)]=(-1)^n\prod_a z_a^{-n}(1-z_a^2)N_1(z)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a,r\le n$

**对象**：Delta_C

**证明路线 / 依赖**：DEF.Nt；DEF.phi；DEF.psi；DEF.Cfun；DEF.chi

#### WEYL.delta.B

- 类型：`statement`；页码：4；定位：(2.6), B

**规范**：$\Delta_B(z)=\det_{a,r}[\psi_r(z_a)]=(-1)^n\prod_a z_a^{-(n-1)}(1-z_a)N_1(z)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a,r\le n$

**对象**：Delta_B

**证明路线 / 依赖**：DEF.Nt；DEF.phi；DEF.psi；DEF.Cfun；DEF.chi

#### WEYL.delta.plus

- 类型：`statement`；页码：4；定位：(2.6), plus

**规范**：$\Delta_+(z)=\det_{a,r}[\chi_r(z_a)]=\prod_a z_a^{-(n-1)}N_1(z)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a,r\le n$

**对象**：Delta_plus

**证明路线 / 依赖**：DEF.Nt；DEF.phi；DEF.psi；DEF.Cfun；DEF.chi

#### WEYL.delta.vandermonde

- 类型：`proof_step`；页码：5；定位：paragraph after (2.6)

**规范**：$\phi_r/(z-z^{-1})$、$\psi_r/(z-1)$、$\chi_r$ 分别是 $z+z^{-1}$ 的首一 $r-1$ 次多项式，故三种分母由 Vandermonde 行列式计算。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Delta_C；Delta_B；Delta_plus

**证明路线 / 依赖**：WEYL.delta.C；WEYL.delta.B；WEYL.delta.plus

#### WEYL.delta.inversion.C

- 类型：`proof_step`；页码：5；定位：last sentence before Section 2.2

**规范**：对单行变量 $z\mapsto z^{-1}$，$\Delta_C$ 乘以 $-1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Delta_C

#### WEYL.delta.inversion.B

- 类型：`proof_step`；页码：5；定位：last sentence before Section 2.2

**规范**：对单行变量 $z\mapsto z^{-1}$，$\Delta_B$ 乘以 $-z^{-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Delta_B

#### WEYL.delta.inversion.plus

- 类型：`proof_step`；页码：5；定位：last sentence before Section 2.2

**规范**：对单行变量 $z\mapsto z^{-1}$，$\Delta_+$ 乘以 $1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Delta_plus

#### DEF.u.first

- 类型：`definition`；页码：5；定位：Section 2.2 first display

**规范**：$u_1^\diamond=[k+1]_\diamond$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$\diamond\in\{C,B,+\}$；$k\ge0$；$1\le r\le n$

**对象**：u.first

#### DEF.utilde.first

- 类型：`definition`；页码：5；定位：Section 2.2 first display

**规范**：$\widetilde u_1^\diamond=[k]_\diamond$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$\diamond\in\{C,B\}$；$k\ge0$；$1\le r\le n$

**对象**：utilde.first

**边界与核查义务**：原文只对 $\diamond=C,B$ 使用 $\widetilde u$。

#### DEF.u.rest

- 类型：`definition`；页码：5；定位：Section 2.2 first display

**规范**：$u_r^\diamond=[k+r]_\diamond+t^{r-1}[k+2-r]_\diamond$，$r\ge2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$\diamond\in\{C,B,+\}$；$k\ge0$；$1\le r\le n$

**对象**：u.rest

#### DEF.utilde.rest

- 类型：`definition`；页码：5；定位：Section 2.2 first display

**规范**：$\widetilde u_r^\diamond=[k+r-1]_\diamond+t^{r-1}[k+1-r]_\diamond$，$r\ge2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$\diamond\in\{C,B\}$；$k\ge0$；$1\le r\le n$

**对象**：utilde.rest

**边界与核查义务**：原文只对 $\diamond=C,B$ 使用 $\widetilde u$。

#### DEF.V.C0

- 类型：`definition`；页码：5；定位：Table 1, C0 row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{C_0}=u_r^C$；所用求值矩阵为 $\Phi^C$，分母为 $\Delta_C$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$

**对象**：V_C0

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### DEF.V.Ct

- 类型：`definition`；页码：5；定位：Table 1, Ct row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{C_t}=[k+r]_C-t^r[k-r]_C$；所用求值矩阵为 $\Phi^C$，分母为 $\Delta_C$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$

**对象**：V_Ct

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### DEF.V.BC

- 类型：`definition`；页码：5；定位：Table 1, BC row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{BC}=u_r^C+\tau\widetilde u_r^C$；所用求值矩阵为 $\Phi^C$，分母为 $\Delta_C$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$；$t=\tau^2$

**对象**：V_BC

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### DEF.V.B0

- 类型：`definition`；页码：5；定位：Table 1, B0 row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{B_0}=u_r^B$；所用求值矩阵为 $\Phi^B$，分母为 $\Delta_B$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$

**对象**：V_B0

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### DEF.V.Bminus

- 类型：`definition`；页码：5；定位：Table 1, Bminus row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{B_-}=[k+r]_B+\tau^{2r-1}[k+1-r]_B$；所用求值矩阵为 $\Phi^B$，分母为 $\Delta_B$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$；$t=\tau^2$

**对象**：V_Bminus

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### DEF.V.Bplus

- 类型：`definition`；页码：5；定位：Table 1, Bplus row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{B_+}=u_r^+$；所用求值矩阵为 $\Phi^+$，分母为 $\Delta_+$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$

**对象**：V_Bplus

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### DEF.V.Bt

- 类型：`definition`；页码：5；定位：Table 1, Bt row

**规范**：$V^\star=(v_1^\star,\ldots,v_n^\star)$；$v_r^{B_t}=u_r^B-t\widetilde u_r^B$；所用求值矩阵为 $\Phi^B$，分母为 $\Delta_B$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k\ge0$；$1\le r\le n$

**对象**：V_Bt

**证明路线 / 依赖**：DEF.u.first；DEF.u.rest；DEF.utilde.first；DEF.utilde.rest

#### CONV.sections3to5

- 类型：`convention`；页码：6；定位：Section 3 opening sentence

**规范**：第 3–5 节全程假设 $n,k\ge1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：n；k

**边界与核查义务**：无须每个引理重写前提；独立规范中逐项显式继承。

#### DEF.Q0

- 类型：`definition`；页码：6；定位：Section 3 initial display

**规范**：$Q_0=\{1,\ldots,n\}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：Q0

#### DEF.index.J

- 类型：`definition`；页码：6；定位：Section 3 initial display

**规范**：$J=\{n+1,\ldots,n+k\}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：J

#### DEF.H

- 类型：`definition`；页码：6；定位：Section 3 initial display

**规范**：$H=\{k+1,\ldots,k+n\}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：H

#### DEF.I

- 类型：`definition`；页码：6；定位：Section 3 initial display

**规范**：$I=\{1,\ldots,k\}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：I

#### DEF.omega

- 类型：`definition`；页码：6；定位：Section 3 initial display

**规范**：$\omega=(-1)^{k(k+1)/2}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：omega

#### DEF.zeta

- 类型：`definition`；页码：6；定位：Section 3 initial display

**规范**：$\zeta=(-1)^{nk}\omega$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：zeta

#### CONV.minor.order

- 类型：`convention`；页码：6；定位：sentence after Section 3 notation

**规范**：所有子集均按递增次序排列；$n\times L$ 矩阵的下标选列，有 $L$ 行的矩阵的下标选行。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：minor

**边界与核查义务**：余子式的符号依赖该排序约定。

#### TRANSFER.normalized

- 类型：`statement`；页码：7；定位：(3.1)

**规范**：$\Phi D=0$、$V^{\mathsf T}C=0$ 且 $\det D_J,\det C_I\ne0$ 时，$P^\star_{n,k}=\dfrac{(-1)^{nk}}{\det D_J\det C_I}\det(D^{\mathsf T}C)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$\det\Phi_{Q_0}=\Delta\ne0$；$\det V_H=1$；$D,C$ 为 $L\times k$

**对象**：P_star；D；C

**证明路线 / 依赖**：T3.1.transfer；P2.2.minor；P2.2.ratio.C0；WEYL.delta.C；WEYL.delta.B；WEYL.delta.plus

**边界与核查义务**：仅需这两个补子式；$\Delta$ 作为形式有理函数非零，特殊数值分母消失须先消去。

#### KERNEL.reflection.Lambda

- 类型：`statement`；页码：7；定位：(3.2), Lambda

**规范**：$\Lambda_i(-m)=-\Lambda_i(m)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le i\le k$

**对象**：Lambda

**证明路线 / 依赖**：COEFF.dot.palindrome

#### KERNEL.reflection.h

- 类型：`statement`；页码：7；定位：(3.2), h

**规范**：$h_i(1-m)=h_i(m)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le i\le k$

**对象**：h

**证明路线 / 依赖**：COEFF.dot.palindrome

#### KERNEL.reflection.hplus

- 类型：`statement`；页码：7；定位：(3.2), hplus

**规范**：$h_i^+(2-m)=h_i^+(m)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le i\le k$

**对象**：hplus

**证明路线 / 依赖**：COEFF.dot.palindrome

#### KERNEL.Lambda.center

- 类型：`proof_step`；页码：8；定位：Lemma 3.3 proof, first sentence

**规范**：$\Lambda_i(0)=0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：Lambda

**证明路线 / 依赖**：DEF.Lambda；COEFF.dot.palindrome

#### KERNEL.rewrite.h

- 类型：`statement`；页码：7；定位：In particular display

**规范**：$h_i(m)=\dot e_{n-i+m}+\dot e_{n-i-m+1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le i\le k$

**对象**：h

**证明路线 / 依赖**：COEFF.dot.palindrome

#### KERNEL.rewrite.hplus

- 类型：`statement`；页码：7；定位：In particular display

**规范**：$h_i^+(m)=\dot e_{n-i+m}+\dot e_{n-i-m+2}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le i\le k$

**对象**：hplus

**证明路线 / 依赖**：COEFF.dot.palindrome

#### DEF.D.C

- 类型：`definition`；页码：7；定位：(3.3), C

**规范**：$D^C_{p,i}=(-1)^p \Lambda_i(p)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$1\le p\le L$；$1\le i\le k$

**对象**：D_C

**证明路线 / 依赖**：DEF.Lambda

#### DEF.D.B

- 类型：`definition`；页码：7；定位：(3.3), B

**规范**：$D^B_{p,i}=(-1)^p h_i(p)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$1\le p\le L$；$1\le i\le k$

**对象**：D_B

**证明路线 / 依赖**：DEF.h

#### DEF.D.plus

- 类型：`definition`；页码：7；定位：(3.3), plus

**规范**：$D^+_{p,i}=(-1)^p h_i^+(p)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$1\le p\le L$；$1\le i\le k$

**对象**：D_plus

**证明路线 / 依赖**：DEF.hplus

#### DEF.affine.fold.C

- 类型：`definition`；页码：8；定位：(3.4), C

**规范**：$C^C(b)_{p,j}=b_j(p)-b_j(-p)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b_j:\mathbb Z\to$ 系数域；$1\le j\le k$；$1\le p\le L$

**对象**：C_C

**边界与核查义务**：序列 $b_j$ 不必有限支撑；与有限核相乘所得展开和有限。

#### DEF.affine.fold.B

- 类型：`definition`；页码：8；定位：(3.4), B

**规范**：$C^B(b)_{p,j}=(-1)^p(b_j(p)+b_j(1-p))$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b_j:\mathbb Z\to$ 系数域；$1\le j\le k$；$1\le p\le L$

**对象**：C_B

**边界与核查义务**：序列 $b_j$ 不必有限支撑；与有限核相乘所得展开和有限。

#### DEF.affine.fold.plus.center

- 类型：`definition`；页码：8；定位：(3.4), plus.center

**规范**：$C^+(b)_{1,j}=-b_j(1)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b_j:\mathbb Z\to$ 系数域；$1\le j\le k$；$1\le p\le L$

**对象**：C_plus.center

**边界与核查义务**：序列 $b_j$ 不必有限支撑；与有限核相乘所得展开和有限。

#### DEF.affine.fold.plus.rest

- 类型：`definition`；页码：8；定位：(3.4), plus.rest

**规范**：$C^+(b)_{p,j}=(-1)^p(b_j(p)+b_j(2-p))$，$2\le p\le L$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b_j:\mathbb Z\to$ 系数域；$1\le j\le k$；$1\le p\le L$

**对象**：C_plus.rest

**边界与核查义务**：序列 $b_j$ 不必有限支撑；与有限核相乘所得展开和有限。

#### FINITE.rows.bound

- 类型：`proof_step`；页码：8；定位：common bound following Lemma 3.3

**规范**：若 $\mathcal E_r=0$ 于 $r\notin[0,N]$，则整行 $\bigl(\mathcal E_{n-i+j-Ky}+\sigma\mathcal E_{n+i+j-Ky-\delta}\bigr)_{j=1}^k$ 只有在 $\left\lceil\frac{n-i+1-N}{K}\right\rceil\le y\le\left\lfloor\frac{n+i+k-\delta}{K}\right\rfloor$ 时可能非零。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$K>0$；$N\ge0$；$\delta\in\{0,1,2\}$；$1\le i\le k$；$2i-\delta\ge0$

**对象**：finite_row_support

**边界与核查义务**：这是允许额外零项的充分有限区间，不是宣称区间内每个移位都非零。

#### FINITE.rows.specialization

- 类型：`proof_step`；页码：8；定位：Take N = ...

**规范**：对 $\Lambda,h,h^+$ 取 $N=2n$，对 $\widehat h$ 取 $N=2n+1$，获得所有实际仿射行和的有限性。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$K>0$

**对象**：Lambda；h；hplus；hhat

**证明路线 / 依赖**：FINITE.rows.bound；CONV.dot.zero；CONV.ddot.zero

#### FINITE.det.multilinear

- 类型：`proof_step`；页码：8；定位：Thus, if A_ij = ...

**规范**：若 $A_{ij}=\sum_{y\in\mathbb Z}w_j(y)F_i(j-Ky)$，由有限的行多线性展开，$\det A=\mathcal J_K[w,F;\mathbb Z^k]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；每一行只有有限多个非零移位，见有限支撑界

**对象**：J_K；A

**证明路线 / 依赖**：DEF.J；FINITE.rows.specialization

**边界与核查义务**：偶格不能直接用此等式，须奇偶投影。

#### PARAM.exponents.nonnegative

- 类型：`proof_step`；页码：8；定位：last paragraph before Section 4

**规范**：各权的参数指数形如 $\frac K2y^2-(j-\eta)y$，其中 $\eta\in\{0,\frac12,1\}$、$K/2\ge k-\eta$、$j-\eta\ge0$，故对整数 $y$ 指数非负。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$1\le j\le k$；$y\in\mathbb Z$

**对象**：weight_exponent

**边界与核查义务**：$y=0$ 指数零；$C_t,j=k,y=1$ 也可指数零。

#### PARAM.exponents.integral.B0

- 类型：`proof_step`；页码：8；定位：In case B0 it is an integer

**规范**：$B_0$ 的指数 $(k+1/2)y^2-(j-1/2)y$ 为整数，因为 $y^2-y$ 为偶数。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$y\in\mathbb Z$；$1\le j\le k$

**对象**：weight_exponent

#### PARAM.exponents.sqrt

- 类型：`proof_step`；页码：8；定位：in the square-root cases ...

**规范**：平方根两例的 $\tau$ 指数是上述 $t$ 指数的两倍，均为非负整数。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$t=\tau^2$

**对象**：weight_exponent；tau

**证明路线 / 依赖**：CONV.sqrt；PARAM.exponents.nonnegative

#### PARAM.polynomial

- 类型：`convention`；页码：8；定位：last sentence of Section 3.3

**规范**：仿射表达式是参数 $t$ 或 $\tau$ 的多项式；反射关系则在相应有理函数域中证明。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：affine_expression

**证明路线 / 依赖**：FINITE.rows.specialization；PARAM.exponents.nonnegative；PARAM.exponents.integral.B0；PARAM.exponents.sqrt

**边界与核查义务**：参数零的结论通过多项式特化，而非带负指数的反射式逐项求值；$0^0$ 对应常数单项式 $1$。

#### DEF.shared.b.support

- 类型：`definition`；页码：11；定位：(5.1), nonzero branch

**规范**：当 $m=j-2ky$、$y\in\mathbb Z$ 时，$b_j(m)=(-1)^y t^{ky^2-(j-1)y}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$1\le j\le k$

**对象**：b_shared

#### DEF.shared.b.off

- 类型：`definition`；页码：11；定位：(5.1), zero branch

**规范**：$m\not\equiv j\pmod{2k}$ 时 $b_j(m)=0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$1\le j\le k$

**对象**：b_shared

#### DEF.shared.Gamma

- 类型：`definition`；页码：11；定位：display below (5.1)

**规范**：$\Gamma_j(m)=(-1)^m(b_j(m)+b_j(2-m))$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le j\le k$

**对象**：Gamma_j

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off

#### KERNEL.hhat.shift

- 类型：`statement`；页码：12；定位：Section 5.3 first paragraph

**规范**：$\widehat h_i(m)=h_i(m)+h_i(m-1)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$；$1\le i\le k$

**对象**：hhat；h

**证明路线 / 依赖**：COEFF.convolution；DEF.h；DEF.hhat

**边界与核查义务**：$B_t$ 使用 $D^B$，没有另造 $\ddot e$ 版本的系数矩阵。

#### DEF.adjacent.a

- 类型：`definition`；页码：12；定位：Section 5.3 definitions

**规范**：$a_j(m)=b_j(m)+b_j(m+1)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b,\Gamma$ 沿用 (5.1)

**对象**：a_adjacent

#### DEF.adjacent.c

- 类型：`definition`；页码：12；定位：Section 5.3 definitions

**规范**：$c_j(m)=(-1)^m(a_j(m)+a_j(1-m))$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b,\Gamma$ 沿用 (5.1)

**对象**：c_adjacent

#### DEF.adjacent.gamma

- 类型：`definition`；页码：12；定位：Section 5.3 definitions

**规范**：$\gamma_j(m)=c_j(m)-tc_j(m-1)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$b,\Gamma$ 沿用 (5.1)

**对象**：gamma_adjacent

#### ADJACENT.support

- 类型：`statement`；页码：12；定位：Thus a_j is supported ...

**规范**：$a_j$ 支撑于模 $2k$ 的两个相邻同余类 $j$ 与 $j-1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）

**对象**：a_adjacent

**证明路线 / 依赖**：DEF.adjacent.a；DEF.shared.b.support；DEF.shared.b.off

#### ADJACENT.shift.symmetry

- 类型：`statement`；页码：12；定位：and c_j(1-m) ...

**规范**：$c_j(1-m)=-c_j(m)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$m\in\mathbb Z$

**对象**：c_adjacent

**证明路线 / 依赖**：DEF.adjacent.c

### A

#### A.1.3

- 类型：`statement`；页码：2；定位：Theorem A, (1.3)

**规范**：$P^{B_n}_{(k^n)}(x;t,0)=\mathcal J_{2k+1}[(-1)^y t^{(k+1/2)y^2-(j-1/2)y},h;\mathbb Z^k]$.

**前提**：$n\ge1,k\ge0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_B0；J_K

**证明路线 / 依赖**：DEF.J；DEF.h；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零按空行列式和空向量约定解释。

#### A.1.4

- 类型：`statement`；页码：2；定位：Theorem A, (1.4)

**规范**：$P^{B_n}_{(k^n)}(x;\tau^2,-\tau)=\mathcal J_{2k}[\tau^{2ky^2-(2j-1)y},h;\mathbb Z^k]$.

**前提**：$n\ge1,k\ge0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_B-；J_K

**证明路线 / 依赖**：DEF.J；DEF.h；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零按空行列式和空向量约定解释。

#### A.1.5

- 类型：`statement`；页码：2；定位：Theorem A, (1.5)

**规范**：$P^{B_n}_{(k^n)}(x;t,1)=\tfrac12\mathcal J_{2k}[(-1)^y t^{ky^2-(j-1)y},h^+;\mathbb Z^k]$.

**前提**：$n,k\ge1$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_B+；J_K

**证明路线 / 依赖**：DEF.J；DEF.hplus；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零另由归一化命题处理，公式本身不适用于 $k=0$。

#### A.1.6

- 类型：`statement`；页码：2；定位：Theorem A, (1.6)

**规范**：$P^{C_n}_{(k^n)}(x;t,0)=\mathcal J_{2k+2}[t^{(k+1)y^2-jy},\Lambda;\mathbb Z^k]$.

**前提**：$n\ge1,k\ge0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_C0；J_K

**证明路线 / 依赖**：DEF.J；DEF.Lambda；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零按空行列式和空向量约定解释。

#### A.1.7

- 类型：`statement`；页码：2；定位：Theorem A, (1.7)

**规范**：$P^{C_n}_{(k^n)}(x;t,t)=\mathcal J_{2k}[t^{ky^2-jy},\Lambda;\mathbb Z^k_{\rm even}]$.

**前提**：$n\ge1,k\ge0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Ct；J_K

**证明路线 / 依赖**：DEF.J；DEF.Lambda；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零按空行列式和空向量约定解释。

#### A.1.8

- 类型：`statement`；页码：2；定位：Theorem A, (1.8)

**规范**：$P^{BC_n}_{(k^n)}(x;\tau^2,-\tau,0)=\mathcal J_{2k+1}[(-1)^y\tau^{(2k+1)y^2-2jy},\Lambda;\mathbb Z^k]$.

**前提**：$n\ge1,k\ge0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_BC；J_K

**证明路线 / 依赖**：DEF.J；DEF.Lambda；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零按空行列式和空向量约定解释。

#### A.widthzero.Bplus

- 类型：`statement`；页码：2；定位：sentence after (1.8)

**规范**：$P^{B_n}_{\varnothing}(x;t,1)=1$.

**前提**：$n\ge1$；$k=0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_B+

**证明路线 / 依赖**：P6.1.Bplus

**边界与核查义务**：将 (1.5) 原样延至 $k=0$ 得到 $1/2$，故必须单独声明规范化端点。

### B

#### B.1.9

- 类型：`statement`；页码：2；定位：Theorem B, (1.9)

**规范**：$P^{B_n}_{(k^n)}(x;t,t)=\tfrac12\mathcal J_{2k}[(-1)^y t^{ky^2-(j-1)y},\widehat h;\mathbb Z^k]$.

**前提**：$n,k\ge1$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bt；J_K

**证明路线 / 依赖**：DEF.J；DEF.hhat；DEF.Weyl.sum

**边界与核查义务**：仅 $n\ge1$；正文不声称秩零版本。；宽度零另由归一化命题处理，公式本身不适用于 $k=0$。

#### B.widthzero.Bt

- 类型：`statement`；页码：2；定位：sentence after (1.9)

**规范**：$P^{B_n}_{\varnothing}(x;t,t)=1$.

**前提**：$n\ge1$；$k=0$；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bt

**证明路线 / 依赖**：P6.1.Bt

**边界与核查义务**：(1.9) 的正宽度外部半系数公式不延伸至宽零。

### L2.1

#### L2.1.2.3

- 类型：`statement`；页码：4；定位：Lemma 2.1, (2.3)

**规范**：$\det_{a,r}[f_r(z_a)]=N_t(z)$.

**前提**：$n\ge1$；$1\le a,r\le n$；变量形式独立

**对象**：alternant；N_t

**证明路线 / 依赖**：DEF.Nt；DEF.fr.first；DEF.fr.rest

**边界与核查义务**：$n=1$ 时仍有效；$t=0$ 或 $\tau=0$ 由多项式恒等式包含。

#### L2.1.2.4

- 类型：`statement`；页码：4；定位：Lemma 2.1, (2.4)

**规范**：$\det_{a,r}[z_a^{n-r}-t^r z_a^{n+r}]=\prod_a(1-tz_a^2)N_t(z)$.

**前提**：$n\ge1$；$1\le a,r\le n$；变量形式独立

**对象**：alternant；N_t

**证明路线 / 依赖**：DEF.Nt；DEF.fr.first；DEF.fr.rest

**边界与核查义务**：$n=1$ 时仍有效；$t=0$ 或 $\tau=0$ 由多项式恒等式包含。

#### L2.1.2.5

- 类型：`statement`；页码：4；定位：Lemma 2.1, (2.5)

**规范**：$\det_{a,r}[z_a^{n-r}+\tau^{2r-1}z_a^{n+r-1}]=\prod_a(1+\tau z_a)N_{\tau^2}(z)$.

**前提**：$n\ge1$；$1\le a,r\le n$；变量形式独立

**对象**：alternant；N_t

**证明路线 / 依赖**：DEF.Nt；DEF.fr.first；DEF.fr.rest

**边界与核查义务**：$n=1$ 时仍有效；$t=0$ 或 $\tau=0$ 由多项式恒等式包含。

#### L2.1.reflection.2.3

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, proportional rows

**规范**：令 $z_b=(tz_a)^{-1}$ 后对应行成比例，乘子为 $t^{1-n}z_a^{2-2n}$；因此有因子 $1-tz_az_b$。

**前提**：$n\ge1$；在其余变量的分式域中作除法

**对象**：alternant

**证明路线 / 依赖**：L2.1.2.3

**边界与核查义务**：这一步中的逆参数不要求最终多项式恒等式在零参数失效。

#### L2.1.reflection.2.4

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, proportional rows

**规范**：令 $z_b=(tz_a)^{-1}$ 后对应行成比例，乘子为 $-t^{-n}z_a^{-2n}$；因此有因子 $1-tz_az_b$。

**前提**：$n\ge1$；在其余变量的分式域中作除法

**对象**：alternant

**证明路线 / 依赖**：L2.1.2.4

**边界与核查义务**：这一步中的逆参数不要求最终多项式恒等式在零参数失效。

#### L2.1.reflection.2.5

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, proportional rows

**规范**：令 $z_b=(tz_a)^{-1}$ 后对应行成比例，乘子为 $\tau^{1-2n}z_a^{1-2n}$；因此有因子 $1-tz_az_b$。第三式中 $t=\tau^2$。

**前提**：$n\ge1$；在其余变量的分式域中作除法

**对象**：alternant

**证明路线 / 依赖**：L2.1.2.5

**边界与核查义务**：这一步中的逆参数不要求最终多项式恒等式在零参数失效。

#### L2.1.rowfactors

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, row factors

**规范**：第二行列式每行有因子 $1-tz_a^2$；第三行列式在 $z_a=-\tau^{-1}$ 消失，故有因子 $1+\tau z_a$.

**前提**：形式多项式计算；中间允许分式域

**对象**：alternant

**证明路线 / 依赖**：L2.1.2.4；L2.1.2.5

**边界与核查义务**：零参数最终用多项式恒等式特化。

#### L2.1.divisibility

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, Gauss lemma

**规范**：三式均交错；反射因子与差因子两两互素。在分式域检验的可除性经 Gauss 引理返回多项式环。

**前提**：形式变量；特征零系数环

**对象**：alternant

**证明路线 / 依赖**：DEF.Nt；L2.1.rowfactors

#### L2.1.degree

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, degree display

**规范**：因子总次数及行列式次数上界依次为 $3\binom n2$、$2n+3\binom n2$、$n+3\binom n2$.

**前提**：$n\ge1$

**对象**：alternant

**证明路线 / 依赖**：L2.1.divisibility

#### L2.1.constant

- 类型：`proof_step`；页码：4；定位：Lemma 2.1 proof, last sentence

**规范**：三式最低次齐次部分均为 $\det[z_a^{n-r}]=\prod_{a<b}(z_a-z_b)$，故商常数为 $1$.

**前提**：$n\ge1$

**对象**：alternant

**证明路线 / 依赖**：L2.1.degree

### P2.2

#### P2.2.ratio.C0

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, C0

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=C0$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_C0；V_C0

**证明路线 / 依赖**：DEF.V.C0；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.ratio.Ct

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, Ct

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=Ct$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Ct；V_Ct

**证明路线 / 依赖**：DEF.V.Ct；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.ratio.BC

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, BC

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=BC$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_BC；V_BC

**证明路线 / 依赖**：DEF.V.BC；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.ratio.B0

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, B0

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=B0$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_B0；V_B0

**证明路线 / 依赖**：DEF.V.B0；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.ratio.Bminus

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, Bminus

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=B_-$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bminus；V_Bminus

**证明路线 / 依赖**：DEF.V.Bminus；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.ratio.Bplus

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, Bplus

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=B_+$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bplus；V_Bplus

**证明路线 / 依赖**：DEF.V.Bplus；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.ratio.Bt

- 类型：`statement`；页码：5；定位：Proposition 2.2, finite representation, Bt

**规范**：$P^{\star}_{n,k}=\det(\Phi V^{\star})/\Delta$，其中 $\star=Bt$ 且采用表 1 对应该行数据。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bt；V_Bt

**证明路线 / 依赖**：DEF.V.Bt；WEYL.inversion.sum

**边界与核查义务**：此命题本身只声称 $k\ge1$；$k=0$ 另见 P6.1。

#### P2.2.leading.rows

- 类型：`proof_step`；页码：6；定位：last paragraph of proof

**规范**：第 $r$ 列的首括号在第 $k+r$ 行放置 $1$；所有其他折叠行均严格小于 $k+r$，故 $V^\star_H$ 为单位上三角。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_star；H

**证明路线 / 依赖**：DEF.V.C0；DEF.V.Ct；DEF.V.BC；DEF.V.B0；DEF.V.Bminus；DEF.V.Bplus；DEF.V.Bt

**边界与核查义务**：严格小于使用 $k\ge1$，包括非正指标折叠；宽零不能直接沿用。

#### P2.2.minor

- 类型：`statement`；页码：5；定位：Proposition 2.2, Moreover

**规范**：$H=\{k+1,\ldots,k+n\}$，$\det V^\star_H=1$（所有七例）。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_star；H

**证明路线 / 依赖**：P2.2.leading.rows

#### P2.2.fold.C0

- 类型：`proof_step`；页码：5；定位：Proposition 2.2 proof, C0

**规范**：$z^{-n-k}f_r(z)$ 经过 $g(z)\mapsto g(z)-g(z^{-1})$ 得 $-\Phi^Cu_r^C$；$n$ 个列负号消去 $\Delta_C$ 的 $(-1)^n$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_C0

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.C0；WEYL.delta.C

#### P2.2.fold.BC

- 类型：`proof_step`；页码：5；定位：Proposition 2.2 proof, BC

**规范**：在 $C_0$ 的行函数上乘 $1+\tau z$，折叠得 $-\Phi^C(u_r^C+\tau\widetilde u_r^C)$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_BC

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.BC；WEYL.delta.C

#### P2.2.fold.Ct

- 类型：`proof_step`；页码：5；定位：Proposition 2.2 proof, Ct

**规范**：用 (2.4) 的 $z^{n-r}-t^rz^{n+r}$ 代替 $f_r$，折叠列为 $-\Phi^C([k+r]_C-t^r[k-r]_C)$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Ct

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.Ct；WEYL.delta.C

#### P2.2.fold.B0

- 类型：`proof_step`；页码：5；定位：Proposition 2.2 proof, B0

**规范**：对 $z^{-(n+k-1)}f_r(z)$ 用 $g(z)\mapsto g(z)-zg(z^{-1})$，得 $-\Phi^Bu_r^B$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_B0

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.B0；WEYL.delta.B

#### P2.2.fold.Bt

- 类型：`proof_step`；页码：5；定位：Proposition 2.2 proof, Bt

**规范**：在 $B_0$ 行函数上乘 $1-tz$，折叠得 $-\Phi^B(u_r^B-t\widetilde u_r^B)$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bt

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.Bt；WEYL.delta.B

#### P2.2.fold.Bminus

- 类型：`proof_step`；页码：6；定位：Proposition 2.2 proof, Bminus

**规范**：用 (2.5) 及移位反对称折叠得到 $B_-$ 列；列负号消去分母的 $(-1)^n$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bminus

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.Bminus；WEYL.delta.B

#### P2.2.fold.Bplus

- 类型：`proof_step`；页码：6；定位：Proposition 2.2 proof, Bplus

**规范**：对 $z^{-(n+k-1)}f_r(z)$ 用 $g(z)\mapsto g(z)+g(z^{-1})$；第一列为 $C_k$，其余列为 $C_{k+r-1}+t^{r-1}C_{k+1-r}$，即 $\Phi^+u_r^+$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bplus

**证明路线 / 依赖**：WEYL.inversion.sum；DEF.V.Bplus；WEYL.delta.plus

**边界与核查义务**：$B_+$ 第一列的归一化由 $\Phi^+_{a,1}=1$ 与 $[1]_+=2e_1$ 共同确定。

### T3.1

#### T3.1.transfer

- 类型：`statement`；页码：6；定位：Theorem 3.1 displayed conclusion

**规范**：$\det(XY)=\dfrac{(-1)^{nk}\det X_{Q_0}\det Y_H}{\det U_J\det Z_I}\det(U^{\mathsf T}Z)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；$\mathbb F$ 为任意域；$L=n+k$；$X\in\mathbb F^{n\times L},Y\in\mathbb F^{L\times n},U,Z\in\mathbb F^{L\times k}$；$XU=0$；$Y^{\mathsf T}Z=0$；$\det X_{Q_0},\det U_J,\det Y_H,\det Z_I$ 均非零；子集与余子式次序见 CONV.minor.order

**对象**：X；Y；U；Z

**证明路线 / 依赖**：DEF.Q0；DEF.index.J；DEF.H；DEF.I；CONV.minor.order

**边界与核查义务**：这里是任意域的线性代数命题，不能误加特征零；分母非零是命题真正前提。

#### T3.1.ranks

- 类型：`proof_step`；页码：6；定位：first sentence of proof

**规范**：四个非零极大子式给出各矩阵满秩；由 $XU=0$ 及维数有 $\operatorname{col}(U)=\ker X$.

**前提**：T3.1.transfer 的全部矩阵、核关系和非零子式前提

**对象**：rank；kernel

**证明路线 / 依赖**：T3.1.transfer

#### T3.1.topforms

- 类型：`proof_step`；页码：6；定位：two multilinear forms in proof

**规范**：$\det[Xv_1\ \cdots\ Xv_n]$ 与 $\det[U\ v_1\ \cdots\ v_n]$ 在 $\mathbb F^L/\operatorname{col}(U)$ 上诱导非零顶形式，故成比例。

**前提**：T3.1.transfer 的全部前提

**对象**：top_forms

**证明路线 / 依赖**：T3.1.ranks

#### T3.1.epsilon

- 类型：`definition`；页码：6；定位：For Q = ...

**规范**：$Q=\{q_1<\cdots<q_n\}$ 时 $\epsilon(Q)=(-1)^{\sum_r(q_r-r)}$.

**前提**：$Q\subseteq\{1,\ldots,L\}$；$|Q|=n$

**对象**：epsilon

#### T3.1.laplace

- 类型：`proof_step`；页码：6；定位：expansion along last n columns

**规范**：$\det[U\ e_{q_1}\ \cdots\ e_{q_n}]=(-1)^{nk}\epsilon(Q)\det U_{Q^c}$.

**前提**：T3.1.transfer 的全部前提；$Q$ 递增排序

**对象**：minor；epsilon

**证明路线 / 依赖**：T3.1.epsilon；CONV.minor.order

#### T3.1.complement.X

- 类型：`proof_step`；页码：6；定位：Consequently, proportionality relation X

**规范**：$\det X_Q=\alpha\epsilon(Q)\det U_{Q^c}$，$\alpha$ 与 $Q$ 无关。

**前提**：T3.1.transfer 的全部前提

**对象**：complementary_minors

**证明路线 / 依赖**：T3.1.topforms；T3.1.laplace

#### T3.1.complement.Y

- 类型：`proof_step`；页码：6；定位：Consequently, proportionality relation Y

**规范**：$\det Y_Q=\beta\epsilon(Q)\det Z_{Q^c}$，$\beta$ 与 $Q$ 无关（由 $Y^{\mathsf T}Z=0$）。

**前提**：T3.1.transfer 的全部前提

**对象**：complementary_minors

**证明路线 / 依赖**：T3.1.topforms；T3.1.laplace

#### T3.1.CauchyBinet

- 类型：`proof_step`；页码：6；定位：last displayed equation

**规范**：$\det(XY)=\alpha\beta\sum_{|Q|=n}\det U_{Q^c}\det Z_{Q^c}=\alpha\beta\det(U^{\mathsf T}Z)$.

**前提**：T3.1.transfer 的全部前提

**对象**：det

**证明路线 / 依赖**：T3.1.complement.X；T3.1.complement.Y

#### T3.1.normalizing.signs

- 类型：`proof_step`；页码：7；定位：first paragraph

**规范**：$\epsilon(Q_0)=1$，$\epsilon(H)=(-1)^{nk}$；分别在 $Q_0,H$ 求值两组比例式，确定传递公式常数。

**前提**：T3.1.transfer 的全部前提

**对象**：epsilon；alpha；beta

**证明路线 / 依赖**：T3.1.epsilon；T3.1.CauchyBinet

### L3.2

#### L3.2.kernel.C

- 类型：`statement`；页码：7；定位：Lemma 3.2, kernel C

**规范**：$\Phi^CD^C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Phi_C；D_C

**证明路线 / 依赖**：DEF.D.C

#### L3.2.kernel.B

- 类型：`statement`；页码：7；定位：Lemma 3.2, kernel B

**规范**：$\Phi^BD^B=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Phi_B；D_B

**证明路线 / 依赖**：DEF.D.B

#### L3.2.kernel.plus

- 类型：`statement`；页码：7；定位：Lemma 3.2, kernel plus

**规范**：$\Phi^+D^+=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Phi_plus；D_plus

**证明路线 / 依赖**：DEF.D.plus

**边界与核查义务**：$D^+$ 第一行不附加额外系数 $2$。

#### L3.2.minor.C

- 类型：`statement`；页码：7；定位：Lemma 3.2, complementary minor C

**规范**：$\det D^C_J=\zeta$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_C；J

**证明路线 / 依赖**：DEF.D.C；DEF.zeta

#### L3.2.minor.B

- 类型：`statement`；页码：7；定位：Lemma 3.2, complementary minor B

**规范**：$\det D^B_J=\zeta$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；J

**证明路线 / 依赖**：DEF.D.B；DEF.zeta

#### L3.2.minor.plus

- 类型：`statement`；页码：7；定位：Lemma 3.2, complementary minor plus

**规范**：$\det D^+_J=2\zeta$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_plus；J

**证明路线 / 依赖**：DEF.D.plus；DEF.zeta

**边界与核查义务**：在 $k=1$ 时 $D^+_J$ 唯一对角元的系数仍为 $2$。

#### L3.2.generating.C

- 类型：`proof_step`；页码：7；定位：Lemma 3.2 proof, generating C

**规范**：$\sum_{m\in\mathbb Z}\Lambda_i(m)z^m=z^{-n}\dot E(z)(z^i-z^{-i})$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$

**对象**：D_C；dotE

**证明路线 / 依赖**：DEF.Edot；COEFF.dot.palindrome

#### L3.2.generating.B

- 类型：`proof_step`；页码：7；定位：Lemma 3.2 proof, generating B

**规范**：$\sum_{m\in\mathbb Z}h_i(m)z^m=z^{-n}\dot E(z)(z^i+z^{1-i})$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$

**对象**：D_B；dotE

**证明路线 / 依赖**：DEF.Edot；COEFF.dot.palindrome

#### L3.2.generating.plus

- 类型：`proof_step`；页码：7；定位：Lemma 3.2 proof, generating plus

**规范**：$\sum_{m\in\mathbb Z}h_i^+(m)z^m=z^{-n}\dot E(z)(z^i+z^{2-i})$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$

**对象**：D_plus；dotE

**证明路线 / 依赖**：DEF.Edot；COEFF.dot.palindrome

#### L3.2.root

- 类型：`proof_step`；页码：7；定位：They vanish at z = -x_a

**规范**：三个有限 Laurent 生成式在 $z=-x_a$ 均为零，因为 $\dot E(-x_a)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le a\le n$

**对象**：dotE

**证明路线 / 依赖**：DEF.Edot；L3.2.generating.C；L3.2.generating.B；L3.2.generating.plus

#### L3.2.pairing.C

- 类型：`proof_step`；页码：7；定位：Lemma 3.2 proof, integer pairing C

**规范**：按 $m\leftrightarrow-m$ 配对得 $\sum_{p\ge1}(-1)^p\Lambda_i(p)\phi_p(x_a)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_C

**证明路线 / 依赖**：L3.2.root；KERNEL.reflection.Lambda

#### L3.2.pairing.B

- 类型：`proof_step`；页码：7；定位：Lemma 3.2 proof, integer pairing B

**规范**：按 $m\leftrightarrow1-m$ 配对得 $\sum_{p\ge1}(-1)^ph_i(p)\psi_p(x_a)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B

**证明路线 / 依赖**：L3.2.root；KERNEL.reflection.h

#### L3.2.pairing.plus

- 类型：`proof_step`；页码：7；定位：Lemma 3.2 proof, integer pairing plus

**规范**：按 $m\leftrightarrow2-m$ 配对，并除以 $x_a$，得 $-h_i^+(1)+\sum_{p\ge2}(-1)^ph_i^+(p)C_{p-1}(x_a)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_plus

**证明路线 / 依赖**：L3.2.root；KERNEL.reflection.hplus

**边界与核查义务**：固定点 $m=1$ 只有单个 $-h_i^+(1)$；由 $\Phi^+_{a,1}=1$ 配合 $D^+_{1,i}=-h_i^+(1)$。

#### L3.2.support.C

- 类型：`proof_step`；页码：7；定位：All three kernels vanish for p > L

**规范**：$p>L\Longrightarrow \Lambda_i(p)=0$，因此无限配对和截断至矩阵的 $L$ 行。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$p\in\mathbb Z$

**对象**：D_C

**证明路线 / 依赖**：CONV.dot.zero；DEF.L

#### L3.2.support.B

- 类型：`proof_step`；页码：7；定位：All three kernels vanish for p > L

**规范**：$p>L\Longrightarrow h_i(p)=0$，因此无限配对和截断至矩阵的 $L$ 行。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$p\in\mathbb Z$

**对象**：D_B

**证明路线 / 依赖**：CONV.dot.zero；DEF.L

#### L3.2.support.plus

- 类型：`proof_step`；页码：7；定位：All three kernels vanish for p > L

**规范**：$p>L\Longrightarrow h_i^+(p)=0$，因此无限配对和截断至矩阵的 $L$ 行。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i\le k$；$p\in\mathbb Z$

**对象**：D_plus

**证明路线 / 依赖**：CONV.dot.zero；DEF.L

#### L3.2.block.C

- 类型：`proof_step`；页码：7；定位：last displayed block formulas, C

**规范**：$D^C_{n+r,i}=(-1)^{n+r}\dot e_{i-r}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le r,i\le k$

**对象**：D_C；J

**证明路线 / 依赖**：DEF.D.C；COEFF.dot.palindrome；CONV.dot.zero

#### L3.2.block.B

- 类型：`proof_step`；页码：7；定位：last displayed block formulas, B

**规范**：$D^B_{n+r,i}=(-1)^{n+r}\dot e_{i-r}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le r,i\le k$

**对象**：D_B；J

**证明路线 / 依赖**：DEF.D.B；COEFF.dot.palindrome；CONV.dot.zero

#### L3.2.block.plus

- 类型：`proof_step`；页码：7；定位：last displayed block formulas, plus

**规范**：$D^+_{n+r,i}=(-1)^{n+r}(\dot e_{i-r}+\dot e_{2-i-r})$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le r,i\le k$

**对象**：D_plus；J

**证明路线 / 依赖**：DEF.D.plus；COEFF.dot.palindrome；CONV.dot.zero

#### L3.2.triangular.CB

- 类型：`proof_step`；页码：7；定位：final paragraph, first two blocks

**规范**：$D^C_J,D^B_J$ 均为上三角，对角元 $(-1)^{n+r}$，乘积为 $(-1)^{nk+k(k+1)/2}=\zeta$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_C；D_B

**证明路线 / 依赖**：L3.2.block.C；L3.2.block.B；COEFF.endpoints

#### L3.2.triangular.plus

- 类型：`proof_step`；页码：7；定位：final paragraph, third block

**规范**：$D^+_J$ 上三角，首对角元 $2(-1)^{n+1}$，其余为 $(-1)^{n+r}$，故其行列式为 $2\zeta$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_plus

**证明路线 / 依赖**：L3.2.block.plus；COEFF.endpoints

**边界与核查义务**：$\dot e_0+\dot e_0=2$ 是倍数来源；不是固定中心配对再计一次。

### L3.3

#### L3.3.unfold.C

- 类型：`statement`；页码：8；定位：(3.5)

**规范**：$((D^C)^{\mathsf T}C^C(b))_{ij}=\sum_{m\in\mathbb Z}(-1)^m\Lambda_i(m)b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i,j\le k$；$b_j$ 可为任意序列

**对象**：D_C；C_C

**证明路线 / 依赖**：DEF.D.C；DEF.affine.fold.C

**边界与核查义务**：右端有限性来自系数核支撑，不来自 $b_j$ 的有限性。

#### L3.3.unfold.B

- 类型：`statement`；页码：8；定位：(3.6)

**规范**：$((D^B)^{\mathsf T}C^B(b))_{ij}=\sum_{m\in\mathbb Z}h_i(m)b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i,j\le k$；$b_j$ 可为任意序列

**对象**：D_B；C_B

**证明路线 / 依赖**：DEF.D.B；DEF.affine.fold.B

**边界与核查义务**：右端有限性来自系数核支撑，不来自 $b_j$ 的有限性。

#### L3.3.unfold.plus

- 类型：`statement`；页码：8；定位：(3.7)

**规范**：$((D^+)^{\mathsf T}C^+(b))_{ij}=\sum_{m\in\mathbb Z}h_i^+(m)b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le i,j\le k$；$b_j$ 可为任意序列

**对象**：D_plus；C_plus

**证明路线 / 依赖**：DEF.D.plus；DEF.affine.fold.plus.center

**边界与核查义务**：右端有限性来自系数核支撑，不来自 $b_j$ 的有限性。

#### L3.3.pairing.C

- 类型：`proof_step`；页码：8；定位：Lemma 3.3 proof, C

**规范**：将 $m=p$ 与 $m=-p$ 配对；用 $\Lambda_i(-p)=-\Lambda_i(p)$ 及 $\Lambda_i(0)=0$。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_C；C_C

**证明路线 / 依赖**：KERNEL.reflection.Lambda；L3.2.support.C

#### L3.3.pairing.B

- 类型：`proof_step`；页码：8；定位：Lemma 3.3 proof, B

**规范**：将 $p\ge1$ 与 $1-p\le0$ 配对，每个整数恰出现一次。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；C_B

**证明路线 / 依赖**：KERNEL.reflection.h；L3.2.support.B

#### L3.3.pairing.plus

- 类型：`proof_step`；页码：8；定位：Lemma 3.3 proof, plus

**规范**：第 $p=1$ 行给 $h_i^+(1)b_j(1)$；$p\ge2$ 与 $2-p\le0$ 配对，固定中心 $m=1$ 仅计算一次。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_plus；C_plus

**证明路线 / 依赖**：KERNEL.reflection.hplus；L3.2.support.plus

**边界与核查义务**：固定中心不得出现额外因子 $2$。

### P4.1

#### P4.1.C0

- 类型：`statement`；页码：9；定位：Proposition 4.1

**规范**：在正宽度，恒等式 A.1.6 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_C0

**证明路线 / 依赖**：A.1.6

#### P4.1.BC

- 类型：`statement`；页码：9；定位：Proposition 4.1

**规范**：在正宽度，恒等式 A.1.8 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_BC

**证明路线 / 依赖**：A.1.8

#### P4.1.K.C0

- 类型：`definition`；页码：9；定位：first sentence of proof

**规范**：$C_0$ 取 $K=2k+2$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：K

#### P4.1.K.BC

- 类型：`definition`；页码：9；定位：first sentence of proof

**规范**：$BC$ 取 $K=2k+1$，$t=\tau^2$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：K；tau

#### P4.1.b.support

- 类型：`definition`；页码：9；定位：first piecewise display

**规范**：当 $m=j+Kq$、$q\in\mathbb Z$ 时，$b_j(m)=t^{Kq^2/2+jq}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le j\le k$；$K$ 按两例指定

**对象**：b_j

**证明路线 / 依赖**：P4.1.K.C0；P4.1.K.BC

#### P4.1.b.off

- 类型：`definition`；页码：9；定位：first piecewise display, zero branch

**规范**：$m\not\equiv j\pmod K$ 时 $b_j(m)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le j\le k$

**对象**：b_j

#### P4.1.c

- 类型：`definition`；页码：9；定位：definition after b_j

**规范**：$c_j(m)=b_j(m)-b_j(-m)$，$C=C^C(b)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_j；C

**证明路线 / 依赖**：DEF.affine.fold.C

#### P4.1.quasiperiod

- 类型：`proof_step`；页码：9；定位：Shifting q gives ...

**规范**：$b_j(m+K)=t^{m+K/2}b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：b_j

**证明路线 / 依赖**：P4.1.b.support；P4.1.b.off

**边界与核查义务**：包括同余类外，两边同时为零；分式域内解释指数。

#### P4.1.reflection.odd

- 类型：`proof_step`；页码：9；定位：(4.1), first equality

**规范**：$c_j(-m)=-c_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：c_j

**证明路线 / 依赖**：P4.1.c

#### P4.1.reflection.affine

- 类型：`proof_step`；页码：9；定位：(4.1), second equality

**规范**：$c_j(m)+t^{m-K/2}c_j(K-m)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：c_j

**证明路线 / 依赖**：P4.1.quasiperiod；P4.1.c

**边界与核查义务**：适用于同余支撑内外；不要额外假设 $m\equiv\pm j$。

#### P4.1.C0.first

- 类型：`proof_step`；页码：9；定位：For C0 ... m = k+1

**规范**：$C_0$ 中 $c_j(k+1)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_j

**证明路线 / 依赖**：P4.1.reflection.affine；P4.1.K.C0

**边界与核查义务**：固定点得 $2c_j(k+1)=0$；所在系数域特征零。

#### P4.1.C0.rest

- 类型：`proof_step`；页码：9；定位：For C0 ... m = k+r

**规范**：$C_0$ 中 $c_j(k+r)+t^{r-1}c_j(k+2-r)=0$（$r\ge2$）。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_j

**证明路线 / 依赖**：P4.1.reflection.affine；P4.1.K.C0

#### P4.1.C0.kernel

- 类型：`proof_step`；页码：9；定位：precisely (VC0)^T C = 0

**规范**：奇延拓与 $[m]_C$ 一致，故 $(V^{C_0})^{\mathsf T}C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_C0；C

**证明路线 / 依赖**：P4.1.C0.first；P4.1.C0.rest；P4.1.reflection.odd；DEF.V.C0

#### P4.1.BC.first

- 类型：`proof_step`；页码：9；定位：For BC, the first column ...

**规范**：$BC$ 中第一有限列给 $c_j(k+1)+\tau c_j(k)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_j

**证明路线 / 依赖**：P4.1.reflection.affine；P4.1.K.BC

#### P4.1.BC.rest

- 类型：`proof_step`；页码：9；定位：four terms display

**规范**：置 $h=k+r$（$r\ge2$），四项分为 $c_j(h)+\tau^{2h-K}c_j(K-h)$ 与 $\tau[c_j(h-1)+\tau^{2(h-1)-K}c_j(K-h+1)]$，两括号均为零。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_j；V_BC

**证明路线 / 依赖**：P4.1.reflection.affine；P4.1.K.BC

#### P4.1.BC.kernel

- 类型：`proof_step`；页码：9；定位：Thus the second kernel relation ...

**规范**：$(V^{BC})^{\mathsf T}C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_BC；C

**证明路线 / 依赖**：P4.1.BC.first；P4.1.BC.rest；P4.1.reflection.odd

#### P4.1.block

- 类型：`proof_step`；页码：9；定位：Because K > 2k ...

**规范**：$K>2k$ 保证 $j$ 与 $-j$ 的同余类不交，首 $k$ 行 $C_I=I_k$，故 $\det C_I=1$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；I

**证明路线 / 依赖**：P4.1.K.C0；P4.1.K.BC；P4.1.b.support；P4.1.b.off

**边界与核查义务**：两个 K 分别为 $2k+2$、$2k+1$；不能套到 $C_t$ 的 $K=2k$。

#### P4.1.A

- 类型：`definition`；页码：9；定位：matrix A display

**规范**：$A_{ij}=\sum_{y\in\mathbb Z}(-1)^{Ky}t^{Ky^2/2-jy}\Lambda_i(j-Ky)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：A

#### P4.1.pairing

- 类型：`proof_step`；页码：9；定位：By (3.5) and y = -q

**规范**：$(D^C)^{\mathsf T}C=A\operatorname{diag}((-1)^1,\ldots,(-1)^k)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_C；C；A

**证明路线 / 依赖**：L3.3.unfold.C；P4.1.A

#### P4.1.weight.C0

- 类型：`proof_step`；页码：9；定位：last paragraph, affine sign C0

**规范**：$K=2k+2$ 时 $(-1)^{Ky}=1$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：A

**证明路线 / 依赖**：P4.1.A

#### P4.1.weight.BC

- 类型：`proof_step`；页码：9；定位：last paragraph, affine sign BC

**规范**：$K=2k+1$ 时 $(-1)^{Ky}=(-1)^y$；$t^{Ky^2/2-jy}=\tau^{(2k+1)y^2-2jy}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：A

**证明路线 / 依赖**：P4.1.A

#### P4.1.normalization

- 类型：`proof_step`；页码：9；定位：last paragraph

**规范**：$\det D^C_J=\zeta=(-1)^{nk}\omega$，$\det C_I=1$，$\det((D^C)^{\mathsf T}C)=\omega\det A$；(3.1) 给 $P^\star_{n,k}=\det A$，行多线性即得两恒等式。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_star；A

**证明路线 / 依赖**：TRANSFER.normalized；L3.2.kernel.C；L3.2.minor.C；P4.1.C0.kernel；P4.1.BC.kernel；P4.1.block；P4.1.pairing；FINITE.det.multilinear

### P4.2

#### P4.2.B0

- 类型：`statement`；页码：9；定位：Proposition 4.2

**规范**：在正宽度，恒等式 A.1.3 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_B0

**证明路线 / 依赖**：A.1.3

#### P4.2.Bminus

- 类型：`statement`；页码：9；定位：Proposition 4.2

**规范**：在正宽度，恒等式 A.1.4 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bminus

**证明路线 / 依赖**：A.1.4

#### P4.2.K.B0

- 类型：`definition`；页码：9；定位：first sentence of proof

**规范**：$B_0$ 取 $K=2k+1$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：K

#### P4.2.K.Bminus

- 类型：`definition`；页码：9；定位：first sentence of proof

**规范**：$B_-$ 取 $K=2k$ 且 $t=\tau^2$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：K

#### P4.2.b.support

- 类型：`definition`；页码：9；定位：piecewise sequence, nonzero branch

**规范**：若 $m=j-Ky$、$y\in\mathbb Z$，则 $b_j(m)=(-1)^{Ky}t^{Ky^2/2-(j-1/2)y}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le j\le k$

**对象**：b_j

#### P4.2.b.off

- 类型：`definition`；页码：9；定位：piecewise sequence, zero branch

**规范**：$m\not\equiv j\pmod K$ 时 $b_j(m)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：b_j

#### P4.2.gamma

- 类型：`definition`；页码：9；定位：last display on page

**规范**：$\gamma_j(m)=(-1)^m(b_j(m)+b_j(1-m))$；$C=C^B(b)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：gamma_j；C

**证明路线 / 依赖**：DEF.affine.fold.B

#### P4.2.quasiperiod

- 类型：`proof_step`；页码：10；定位：first sentence

**规范**：$b_j(m+K)=(-1)^Kt^{m+(K-1)/2}b_j(m)$，由 $y\mapsto y-1$ 得。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：b_j

**证明路线 / 依赖**：P4.2.b.support；P4.2.b.off

**边界与核查义务**：同余类外成立；负指数按分式域解释。

#### P4.2.reflection.shift

- 类型：`proof_step`；页码：10；定位：(4.2), first equality

**规范**：$\gamma_j(1-m)=-\gamma_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：gamma_j

**证明路线 / 依赖**：P4.2.gamma

#### P4.2.reflection.affine

- 类型：`proof_step`；页码：10；定位：(4.2), second equality

**规范**：$\gamma_j(m)=-t^{m-(K+1)/2}\gamma_j(K+1-m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：gamma_j

**证明路线 / 依赖**：P4.2.quasiperiod

**边界与核查义务**：无论 K 奇偶，最前面均为负号；不能删去偶 K 的负号。

#### P4.2.parity.sign

- 类型：`proof_step`；页码：10；定位：For example ...

**规范**：$b_j(K+1-m)$ 与 $b_j(m-K)$ 相对反射项获得同一因子 $(-1)^Kt^{(K+1)/2-m}$；$\gamma$ 的 $(-1)^m$ 将其转成 (4.2) 的统一负号。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：gamma_j

**证明路线 / 依赖**：P4.2.quasiperiod；P4.2.gamma

#### P4.2.B0.first

- 类型：`proof_step`；页码：10；定位：For B0, the fixed index ...

**规范**：$B_0$ 中 $\gamma_j(k+1)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：gamma_j

**证明路线 / 依赖**：P4.2.reflection.affine；P4.2.K.B0

**边界与核查义务**：固定点反射在特征零域中迫使值零。

#### P4.2.B0.rest

- 类型：`proof_step`；页码：10；定位：remaining columns ...

**规范**：$B_0$ 中 $\gamma_j(k+r)+t^{r-1}\gamma_j(k+2-r)=0$（$r\ge2$）。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：gamma_j

**证明路线 / 依赖**：P4.2.reflection.affine

#### P4.2.Bminus.columns

- 类型：`proof_step`；页码：10；定位：For Bminus ...

**规范**：$B_-$ 中 $\gamma_j(k+r)+\tau^{2r-1}\gamma_j(k+1-r)=0$（包括 $r=1$）。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：gamma_j

**证明路线 / 依赖**：P4.2.reflection.affine；P4.2.K.Bminus

#### P4.2.kernel

- 类型：`proof_step`；页码：10；定位：first reflection makes evaluation ...

**规范**：由 $\gamma_j(1-m)=-\gamma_j(m)$，$[m]_B$ 的求值等于 $\gamma_j(m)$，故两个有限矩阵均有 $V^{\mathsf T}C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_B0；V_Bminus；C

**证明路线 / 依赖**：P4.2.reflection.shift；P4.2.B0.first；P4.2.B0.rest；P4.2.Bminus.columns

#### P4.2.block.direct

- 类型：`proof_step`；页码：10；定位：For 1 <= p,j <= k ...

**规范**：$b_j(p)=\delta_{p,j}$，$b_j(1-p)=0$，因为 $1\le j+p-1\le2k-1<K$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le p,j\le k$

**对象**：b_j；I

**证明路线 / 依赖**：P4.2.b.support；P4.2.b.off

**边界与核查义务**：适用于 k=1；反射同余类不与首块相交。

#### P4.2.block

- 类型：`proof_step`；页码：10；定位：Thus C_I ...

**规范**：$C_I=\operatorname{diag}((-1)^1,\ldots,(-1)^k)$，故 $\det C_I=\omega$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；I

**证明路线 / 依赖**：P4.2.block.direct；P4.2.gamma

#### P4.2.pairing

- 类型：`proof_step`；页码：10；定位：common pairing display

**规范**：$((D^B)^{\mathsf T}C)_{ij}=A_{ij}=\sum_{y\in\mathbb Z}(-1)^{Ky}t^{Ky^2/2-(j-1/2)y}h_i(j-Ky)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；C；A

**证明路线 / 依赖**：L3.3.unfold.B；P4.2.b.support

#### P4.2.weight.B0

- 类型：`proof_step`；页码：10；定位：last paragraph sign distinction

**规范**：奇数 $K=2k+1$ 给符号 $(-1)^y$ 及 (1.3) 的权。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：A

**证明路线 / 依赖**：P4.2.pairing

#### P4.2.weight.Bminus

- 类型：`proof_step`；页码：10；定位：last paragraph sign distinction

**规范**：偶数 $K=2k$ 无仿射符号；$\tau$ 指数为 $2ky^2-(2j-1)y$，给 (1.4) 的权。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：A

**证明路线 / 依赖**：P4.2.pairing

#### P4.2.normalization

- 类型：`proof_step`；页码：10；定位：last paragraph

**规范**：由 $\det D^B_J=\zeta$ 与 $\det C_I=\omega$，(3.1) 的常数为 $1$；$P^\star_{n,k}=\det A$，再作有限行展开。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_star；A

**证明路线 / 依赖**：TRANSFER.normalized；L3.2.kernel.B；L3.2.minor.B；P4.2.kernel；P4.2.block；P4.2.pairing；FINITE.det.multilinear

### P5.1

#### P5.1.identity

- 类型：`statement`；页码：10；定位：Proposition 5.1

**规范**：正宽度下恒等式 (1.7) 即 A.1.7 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Ct

**证明路线 / 依赖**：A.1.7

#### P5.1.K

- 类型：`definition`；页码：10；定位：first sentence of proof

**规范**：$K=2k$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：K

#### P5.1.b.support

- 类型：`definition`；页码：10；定位：piecewise definition, nonzero branch

**规范**：当 $m=j+2kq$、$q\in\mathbb Z$ 时，$b_j(m)=(-1)^q t^{kq^2+jq}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le j\le k$

**对象**：b_j

#### P5.1.b.off

- 类型：`definition`；页码：10；定位：piecewise definition, zero branch

**规范**：$m\not\equiv j\pmod{2k}$ 时 $b_j(m)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：b_j

#### P5.1.c

- 类型：`definition`；页码：10；定位：Let c_j ...

**规范**：$c_j(m)=b_j(m)-b_j(-m)$，$C=C^C(b)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_j；C

#### P5.1.quasiperiod

- 类型：`proof_step`；页码：10；定位：quasiperiodicity sentence

**规范**：$b_j(m+2k)=-t^{m+k}b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：b_j

**证明路线 / 依赖**：P5.1.b.support；P5.1.b.off

#### P5.1.reflection.odd

- 类型：`proof_step`；页码：10；定位：reflection display, first equality

**规范**：$c_j(-m)=-c_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：c_j

**证明路线 / 依赖**：P5.1.c

#### P5.1.reflection.affine

- 类型：`proof_step`；页码：10；定位：reflection display, second equality

**规范**：$c_j(m)=t^{m-k}c_j(2k-m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：c_j

**证明路线 / 依赖**：P5.1.quasiperiod

#### P5.1.kernel

- 类型：`proof_step`；页码：10；定位：At m = k+r ...

**规范**：在 $m=k+r$ 得 $c_j(k+r)-t^r c_j(k-r)=0$；故 $(V^{C_t})^{\mathsf T}C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le r\le n$

**对象**：V_Ct；C

**证明路线 / 依赖**：P5.1.reflection.affine；P5.1.reflection.odd；DEF.V.Ct

#### P5.1.fixed.residue

- 类型：`proof_step`；页码：10；定位：last displayed equality

**规范**：$j=k$ 时 $k\equiv-k\pmod{2k}$，且 $c_k(k+2kq)=2(-1)^q t^{kq(q+1)}$（$q\in\mathbb Z$）。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_k

**证明路线 / 依赖**：P5.1.b.support；P5.1.c

**边界与核查义务**：重合同余类的两项相加，不相消；$q=0$ 给 $c_k(k)=2$。

#### P5.1.block

- 类型：`proof_step`；页码：11；定位：first paragraph

**规范**：$j<k$ 时正负同余类仍不交，故 $C_I=\operatorname{diag}(1,\ldots,1,2)$，$\det C_I=2$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；I

**证明路线 / 依赖**：P5.1.fixed.residue

**边界与核查义务**：$k=1$ 时整个块就是单元 $[2]$。

#### P5.1.a

- 类型：`definition`；页码：11；定位：Write ... a_ij

**规范**：$a_{ij}(y)=t^{ky^2-jy}\Lambda_i(j-2ky)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：a_ij

#### P5.1.Aplus

- 类型：`definition`；页码：11；定位：Write ... Aplus

**规范**：$A^+_{ij}=\sum_y a_{ij}(y)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Aplus

**证明路线 / 依赖**：P5.1.a

#### P5.1.Aminus

- 类型：`definition`；页码：11；定位：Write ... Aminus

**规范**：$A^-_{ij}=\sum_y(-1)^y a_{ij}(y)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Aminus

**证明路线 / 依赖**：P5.1.a

#### P5.1.pairing

- 类型：`proof_step`；页码：11；定位：pairing (3.5) sentence

**规范**：令 $y=-q$，$(D^C)^{\mathsf T}C=A^-\operatorname{diag}((-1)^1,\ldots,(-1)^k)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_C；C；Aminus

**证明路线 / 依赖**：L3.3.unfold.C；P5.1.b.support；P5.1.Aminus

#### P5.1.half.det

- 类型：`proof_step`；页码：11；定位：Thus the fixed-residue minor ...

**规范**：$P^{C_t}_{n,k}=\tfrac12\det A^-$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Ct；Aminus

**证明路线 / 依赖**：TRANSFER.normalized；L3.2.kernel.C；L3.2.minor.C；P5.1.kernel；P5.1.block；P5.1.pairing

#### P5.1.parity.projector

- 类型：`proof_step`；页码：11；定位：parity projector display

**规范**：$\sum_{y\in\mathbb Z^k_{\rm even}}\det[a_{ij}(y_i)]=\tfrac12(\det A^++\det A^-)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Z_even；Aplus；Aminus

**证明路线 / 依赖**：DEF.even.lattice；FINITE.det.multilinear；P5.1.Aplus；P5.1.Aminus

**边界与核查义务**：这是向量总和偶性的投影，不是各分量都偶数。

#### P5.1.involution.exponent

- 类型：`proof_step`；页码：11；定位：In the last column ... first clause

**规范**：末列 $j=k$ 中 $y\mapsto1-y$ 保持指数 $ky^2-ky$，并将 $k-2ky$ 变为其负数。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$y\in\mathbb Z$

**对象**：a_ik

**证明路线 / 依赖**：P5.1.a

#### P5.1.involution.sign

- 类型：`proof_step`；页码：11；定位：Since Lambda_i is odd ...

**规范**：$a_{i,k}(1-y)=-a_{i,k}(y)$；整数上无不动点的对合使 $A^+$ 末列全零。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Aplus

**证明路线 / 依赖**：P5.1.involution.exponent；KERNEL.reflection.Lambda

**边界与核查义务**：$k=1$ 仍有一列，因而该行列式为零。

#### P5.1.even.lattice

- 类型：`proof_step`；页码：11；定位：last sentence of proof

**规范**：$\det A^+=0$，故偶格和等于 $\tfrac12\det A^-=P^{C_t}_{n,k}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Ct；Z_even

**证明路线 / 依赖**：P5.1.parity.projector；P5.1.involution.sign；P5.1.half.det

**边界与核查义务**：不能把 $P^{C_t}$ 换成未投影的全格和。

### L5.2

#### L5.2.quasiperiod

- 类型：`statement`；页码：11；定位：Lemma 5.2, (5.2) quasiperiod

**规范**：$b_j(m+2k)=-t^{m+k-1}b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；序列由 (5.1) 定义

**对象**：Gamma_j；b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off；DEF.shared.Gamma

**边界与核查义务**：允许负参数指数的有理函数恒等式。

#### L5.2.center.symmetry

- 类型：`statement`；页码：11；定位：Lemma 5.2, (5.2) center.symmetry

**规范**：$\Gamma_j(2-m)=\Gamma_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；序列由 (5.1) 定义

**对象**：Gamma_j；b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off；DEF.shared.Gamma

#### L5.2.affine.reflection

- 类型：`statement`；页码：11；定位：Lemma 5.2, (5.2) affine.reflection

**规范**：$\Gamma_j(m)=-t^{m-k-1}\Gamma_j(2k+2-m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；序列由 (5.1) 定义

**对象**：Gamma_j；b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off；DEF.shared.Gamma

**边界与核查义务**：允许负参数指数的有理函数恒等式。

#### L5.2.fixed.zero

- 类型：`statement`；页码：11；定位：Lemma 5.2, (5.2) fixed.zero

**规范**：$\Gamma_j(k+1)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；序列由 (5.1) 定义

**对象**：Gamma_j；b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off；DEF.shared.Gamma

**边界与核查义务**：固定点反射系数是 $-1$，在特征零域得零。

#### L5.2.shift.proof

- 类型：`proof_step`；页码：11；定位：first sentence of proof

**规范**：由 (5.1) 中 $y\mapsto y-1$ 得 $b$ 的准周期式；$\Gamma$ 的中心对称由定义直接得到。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Gamma_j；b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.Gamma

#### L5.2.shift.right

- 类型：`proof_step`；页码：11；定位：proof, paired equations

**规范**：$b_j(2k+2-m)=-t^{k+1-m}b_j(2-m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：b_shared

**证明路线 / 依赖**：L5.2.quasiperiod

#### L5.2.shift.left

- 类型：`proof_step`；页码：11；定位：proof, paired equations

**规范**：$b_j(m-2k)=-t^{k+1-m}b_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$

**对象**：b_shared

**证明路线 / 依赖**：L5.2.quasiperiod

#### L5.2.reflection.proof

- 类型：`proof_step`；页码：11；定位：last paragraph of proof

**规范**：$m$ 与 $2k+2-m$ 同奇偶，将两条移位式相加得 $\Gamma$ 的仿射反射式。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：Gamma_j

**证明路线 / 依赖**：L5.2.shift.right；L5.2.shift.left；DEF.shared.Gamma

### P5.3

#### P5.3.identity

- 类型：`statement`；页码：12；定位：Proposition 5.3

**规范**：正宽度下 (1.5) 即 A.1.5 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bplus

**证明路线 / 依赖**：A.1.5

#### P5.3.C

- 类型：`definition`；页码：12；定位：first sentence of proof

**规范**：$C=C^+(b)$，$b$ 为 (5.1) 序列。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C

**证明路线 / 依赖**：DEF.affine.fold.plus.center；DEF.affine.fold.plus.rest；DEF.shared.b.support

#### P5.3.center

- 类型：`proof_step`；页码：12；定位：first displayed equality

**规范**：$C_{1,j}=-b_j(1)$；$[1]_+^{\mathsf T}C_{\bullet,j}=2C_{1,j}=-2b_j(1)=\Gamma_j(1)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；Gamma_j

**证明路线 / 依赖**：P5.3.C；DEF.fold.plus.center；DEF.shared.Gamma

**边界与核查义务**：这是有限括号中心的系数 $2$；仿射配对中心本身仅算一次。

#### P5.3.bracket.eval

- 类型：`proof_step`；页码：12；定位：Together with symmetry ...

**规范**：结合 $\Gamma_j(2-m)=\Gamma_j(m)$，每个允许的 $[m]_+$ 对 $C$ 求值等于 $\Gamma_j(m)$，包括固定中心。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；Gamma_j

**证明路线 / 依赖**：P5.3.center；L5.2.center.symmetry；DEF.fold.plus.high；DEF.fold.plus.nonpositive

#### P5.3.first.column

- 类型：`proof_step`；页码：12；定位：first column evaluates ...

**规范**：第一有限列对 $C$ 求值为 $\Gamma_j(k+1)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bplus；C

**证明路线 / 依赖**：P5.3.bracket.eval；L5.2.fixed.zero

#### P5.3.rest.columns

- 类型：`proof_step`；页码：12；定位：and the others to ...

**规范**：其余有限列给 $\Gamma_j(k+r)+t^{r-1}\Gamma_j(k+2-r)=0$（$r\ge2$）。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bplus；C

**证明路线 / 依赖**：L5.2.affine.reflection；P5.3.bracket.eval

#### P5.3.kernel

- 类型：`proof_step`；页码：12；定位：therefore gives (VB+)^T C = 0

**规范**：$(V^{B_+})^{\mathsf T}C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bplus；C

**证明路线 / 依赖**：P5.3.first.column；P5.3.rest.columns

#### P5.3.block.center

- 类型：`proof_step`；页码：12；定位：Indeed b_j(1) ...

**规范**：$b_j(1)=\delta_{j,1}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off

#### P5.3.block.rest

- 类型：`proof_step`；页码：12；定位：for 2 <= p <= k ...

**规范**：$2\le p\le k$ 时 $b_j(p)=\delta_{p,j}$；反射项若非零须 $2ky=j+p-2\in\{1,\ldots,2k-2\}$，不可能。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le j\le k$

**对象**：b_shared

**证明路线 / 依赖**：DEF.shared.b.support；DEF.shared.b.off

**边界与核查义务**：$k=1$ 时该行范围为空，只保留中心行。

#### P5.3.block

- 类型：`proof_step`；页码：12；定位：The first k rows ...

**规范**：$C_I=\operatorname{diag}((-1)^1,\ldots,(-1)^k)$，$\det C_I=\omega$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；I

**证明路线 / 依赖**：P5.3.block.center；P5.3.block.rest；P5.3.C

#### P5.3.doubling.source

- 类型：`proof_step`；页码：12；定位：The factor 2 occurs instead ...

**规范**：倍数 $2$ 由 $\det D^+_J=2\zeta$ 提供，其首对角系数为 $\dot e_0+\dot e_0$；$C_I$ 没有倍数 $2$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_plus；C

**证明路线 / 依赖**：L3.2.minor.plus；L3.2.triangular.plus；P5.3.block

#### P5.3.pairing

- 类型：`proof_step`；页码：12；定位：By (3.7), displayed sum

**规范**：$((D^+)^{\mathsf T}C)_{ij}=A^{B_+}_{ij}=\sum_y(-1)^yt^{ky^2-(j-1)y}h_i^+(j-2ky)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_plus；C；A_Bplus

**证明路线 / 依赖**：L3.3.unfold.plus；DEF.shared.b.support

**边界与核查义务**：中心仅贡献 $h_i^+(1)b_j(1)$，没有加倍。

#### P5.3.normalization

- 类型：`proof_step`；页码：12；定位：last sentence of proof

**规范**：由 (3.1)，$P^{B_+}_{n,k}=\tfrac12\det A^{B_+}$；有限行多线性展开给 (1.5)。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bplus；A_Bplus

**证明路线 / 依赖**：TRANSFER.normalized；L3.2.kernel.plus；P5.3.kernel；P5.3.block；P5.3.doubling.source；P5.3.pairing；FINITE.det.multilinear

### L5.4

#### L5.4.5.3

- 类型：`statement`；页码：12；定位：Lemma 5.4, (5.3)

**规范**：$c_j(m)=\Gamma_j(m)-\Gamma_j(m+1)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；相邻序列定义如本节

**对象**：c_adjacent；gamma_adjacent；Gamma_j

**证明路线 / 依赖**：DEF.adjacent.a；DEF.adjacent.c；DEF.adjacent.gamma；DEF.shared.Gamma；L5.2.affine.reflection

#### L5.4.5.4

- 类型：`statement`；页码：12；定位：Lemma 5.4, (5.4)

**规范**：$\gamma_j(m)=(1+t)\Gamma_j(m)-\Gamma_j(m+1)-t\Gamma_j(m-1)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；相邻序列定义如本节

**对象**：c_adjacent；gamma_adjacent；Gamma_j

**证明路线 / 依赖**：DEF.adjacent.a；DEF.adjacent.c；DEF.adjacent.gamma；DEF.shared.Gamma；L5.2.affine.reflection

#### L5.4.5.5

- 类型：`statement`；页码：12；定位：Lemma 5.4, (5.5)

**规范**：$\gamma_j(m)=-t^{m-k-1}\gamma_j(2k+2-m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；相邻序列定义如本节

**对象**：c_adjacent；gamma_adjacent；Gamma_j

**证明路线 / 依赖**：DEF.adjacent.a；DEF.adjacent.c；DEF.adjacent.gamma；DEF.shared.Gamma；L5.2.affine.reflection

#### L5.4.fixed.zero

- 类型：`statement`；页码：12；定位：Lemma 5.4, In particular

**规范**：$\gamma_j(k+1)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$m\in\mathbb Z$；$1\le j\le k$；相邻序列定义如本节

**对象**：c_adjacent；gamma_adjacent；Gamma_j

**证明路线 / 依赖**：DEF.adjacent.a；DEF.adjacent.c；DEF.adjacent.gamma；DEF.shared.Gamma；L5.2.affine.reflection

**边界与核查义务**：固定点零值使用特征零。

#### L5.4.expansion

- 类型：`proof_step`；页码：12；定位：first sentence of proof

**规范**：展开定义得 (5.3)；再减去 $tc_j(m-1)$ 得 (5.4)。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：c_adjacent；gamma_adjacent

**证明路线 / 依赖**：DEF.adjacent.c；DEF.adjacent.gamma；L5.4.5.3

#### L5.4.reflection.proof

- 类型：`proof_step`；页码：12；定位：proof, T and d display

**规范**：置 $T=2k+2,d=m-k-1$，在 $m,m+1,m-1$ 对 $\Gamma$ 应用 (5.2)，得 $\gamma_j(m)=-t^d[(1+t)\Gamma_j(T-m)-t\Gamma_j(T-m-1)-\Gamma_j(T-m+1)]=-t^d\gamma_j(T-m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：gamma_adjacent

**证明路线 / 依赖**：L5.4.5.4；L5.2.affine.reflection

**边界与核查义务**：相邻两项的参数幂分别转成系数 $t$ 和 $1$，次序不可互换。

### P5.5

#### P5.5.identity

- 类型：`statement`；页码：13；定位：Proposition 5.5

**规范**：正宽度下 (1.9) 即 B.1.9 成立。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bt

**证明路线 / 依赖**：B.1.9

#### P5.5.C

- 类型：`definition`；页码：13；定位：first sentence of proof

**规范**：$C=C^B(a)$，故 $C_{p,j}=c_j(p)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；c_adjacent

**证明路线 / 依赖**：DEF.affine.fold.B；DEF.adjacent.c

#### P5.5.bracket.eval

- 类型：`proof_step`；页码：13；定位：implicit in finite-column evaluation

**规范**：由 $c_j(1-m)=-c_j(m)$，有限括号 $[m]_B$ 对 $C$ 求值为 $c_j(m)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；c_adjacent

**证明路线 / 依赖**：ADJACENT.shift.symmetry；DEF.fold.B.positive；DEF.fold.B.nonpositive

#### P5.5.first.column

- 类型：`proof_step`；页码：13；定位：first display

**规范**：$([k+1]_B-t[k]_B)^{\mathsf T}C_{\bullet,j}=\gamma_j(k+1)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bt；C

**证明路线 / 依赖**：P5.5.bracket.eval；DEF.adjacent.gamma；L5.4.fixed.zero

#### P5.5.rest.columns

- 类型：`proof_step`；页码：13；定位：For r >= 2 ...

**规范**：对 $r\ge2$，$u_r^B-t\widetilde u_r^B$ 的四项对 $C$ 求值为 $\gamma_j(k+r)+t^{r-1}\gamma_j(k+2-r)=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bt；C

**证明路线 / 依赖**：P5.5.bracket.eval；DEF.V.Bt；L5.4.5.5

#### P5.5.kernel

- 类型：`proof_step`；页码：13；定位：Hence ...

**规范**：$(V^{B_t})^{\mathsf T}C=0$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：V_Bt；C

**证明路线 / 依赖**：P5.5.first.column；P5.5.rest.columns

#### P5.5.block.a.direct

- 类型：`proof_step`；页码：13；定位：a_j(p) display, first equality

**规范**：$a_j(p)=\delta_{p,j}+\delta_{p,j-1}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le p,j\le k$；首块只有 $y=0$ 可贡献

**对象**：a_adjacent

**证明路线 / 依赖**：DEF.adjacent.a；DEF.shared.b.support；DEF.shared.b.off

#### P5.5.block.a.reflected

- 类型：`proof_step`；页码：13；定位：a_j(1-p) display, second equality

**规范**：$a_j(1-p)=\delta_{p,1}\delta_{j,1}$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le p,j\le k$

**对象**：a_adjacent

**证明路线 / 依赖**：DEF.adjacent.a；DEF.shared.b.support；DEF.shared.b.off

**边界与核查义务**：两个同余条件为 $2ky=j+p-1$ 或 $2ky=j+p-2$；仅后一种在 $p=j=1$ 可发生。

#### P5.5.block.entries

- 类型：`proof_step`；页码：13；定位：Therefore C_pj display

**规范**：$C_{p,j}=(-1)^p(\delta_{p,j}+\delta_{p,j-1}+\delta_{p,1}\delta_{j,1})$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$1\le p,j\le k$

**对象**：C；I

**证明路线 / 依赖**：P5.5.C；P5.5.block.a.direct；P5.5.block.a.reflected

#### P5.5.block.triangular

- 类型：`proof_step`；页码：13；定位：This block is upper bidiagonal ...

**规范**：$C_I$ 上双对角，对角线依次为 $-2,1,-1,1,\ldots$，所以 $\det C_I=2\omega$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：C；I

**证明路线 / 依赖**：P5.5.block.entries

**边界与核查义务**：$k=1$ 时是 $[-2]$，其行列式等于 $2\omega=-2$。

#### P5.5.no.D.doubling

- 类型：`proof_step`；页码：13；定位：There is no doubling ...

**规范**：$\det D^B_J=\zeta$；倍数 $2$ 完全来自相邻同余类首块的重叠。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；C

**证明路线 / 依赖**：L3.2.minor.B；P5.5.block.triangular

#### P5.5.pairing.unfold

- 类型：`proof_step`；页码：13；定位：common pairing, first line

**规范**：$((D^B)^{\mathsf T}C)_{ij}=\sum_m h_i(m)(b_j(m)+b_j(m+1))$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；C

**证明路线 / 依赖**：L3.3.unfold.B；DEF.adjacent.a

#### P5.5.pairing.shift

- 类型：`proof_step`；页码：13；定位：common pairing, second line

**规范**：上式 $=\sum_y(-1)^yt^{ky^2-(j-1)y}[h_i(j-2ky)+h_i(j-1-2ky)]$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；C

**证明路线 / 依赖**：P5.5.pairing.unfold；DEF.shared.b.support

#### P5.5.pairing.hhat

- 类型：`proof_step`；页码：13；定位：common pairing, third line

**规范**：上式 $=\sum_y(-1)^yt^{ky^2-(j-1)y}\widehat h_i(j-2ky)$.

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：D_B；C；hhat

**证明路线 / 依赖**：P5.5.pairing.shift；KERNEL.hhat.shift

#### P5.5.normalization

- 类型：`proof_step`；页码：13；定位：last sentence of proof

**规范**：(3.1) 给出上述 $k\times k$ 仿射矩阵行列式的一半；有限行展开即得 Theorem B。

**前提**：$n,k\ge1$（第 3–5 节的全局前提，亦为正宽度有限表示的前提）；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：P_Bt

**证明路线 / 依赖**：TRANSFER.normalized；L3.2.kernel.B；P5.5.kernel；P5.5.block.triangular；P5.5.no.D.doubling；P5.5.pairing.hhat；FINITE.det.multilinear

### P6.1

#### P6.1.C0

- 类型：`statement`；页码：13；定位：Proposition 6.1, C0

**规范**：$P^\star_{n,0}=1$，其中 $\star=C0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_C0

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.C0；DEF.nu.zero.C0

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.Ct

- 类型：`statement`；页码：13；定位：Proposition 6.1, Ct

**规范**：$P^\star_{n,0}=1$，其中 $\star=Ct$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_Ct

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.Ct；DEF.nu.zero.Ct

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.BC

- 类型：`statement`；页码：13；定位：Proposition 6.1, BC

**规范**：$P^\star_{n,0}=1$，其中 $\star=BC$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_BC

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.BC；DEF.nu.zero.BC

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.B0

- 类型：`statement`；页码：13；定位：Proposition 6.1, B0

**规范**：$P^\star_{n,0}=1$，其中 $\star=B0$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_B0

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.B0；DEF.nu.zero.B0

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.Bminus

- 类型：`statement`；页码：13；定位：Proposition 6.1, Bminus

**规范**：$P^\star_{n,0}=1$，其中 $\star=B_-$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_Bminus

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.Bminus；DEF.nu.zero.Bminus

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.Bplus

- 类型：`statement`；页码：13；定位：Proposition 6.1, Bplus

**规范**：$P^\star_{n,0}=1$，其中 $\star=B_+$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_Bplus

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.Bplus；DEF.nu.zero.Bplus

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.Bt

- 类型：`statement`；页码：13；定位：Proposition 6.1, Bt

**规范**：$P^\star_{n,0}=1$，其中 $\star=Bt$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_Bt

**证明路线 / 依赖**：P6.1.finite.zero；P6.1.diagonal.Bt；DEF.nu.zero.Bt

**边界与核查义务**：归一化因子的可去奇点在消去后解释；不增加数值非零前提。

#### P6.1.A.endpoints

- 类型：`statement`；页码：13；定位：Consequently ...

**规范**：Theorem A 中没有外部半系数的五式 (1.3),(1.4),(1.6),(1.7),(1.8) 也在 $k=0$ 成立。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：A

**证明路线 / 依赖**：CONV.empty.det；CONV.empty.vector；CONV.empty.noeval；P6.1.C0；P6.1.Ct；P6.1.BC；P6.1.B0；P6.1.Bminus

**边界与核查义务**：不包括 (1.5) 或 Theorem B 的半行列式式。

#### P6.1.finite.zero

- 类型：`proof_step`；页码：13；定位：proof displayed equality

**规范**：$\nu_\star(0)P^\star_{n,0}=\det(\Phi V^\star|_{k=0})/\Delta$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：P_star；V_star

**证明路线 / 依赖**：WEYL.inversion.sum；P2.2.fold.C0；P2.2.fold.Ct；P2.2.fold.BC；P2.2.fold.B0；P2.2.fold.Bminus；P2.2.fold.Bplus；P2.2.fold.Bt

**边界与核查义务**：这是重新使用有限交错化与折叠计算，不是将 P2.2 的正宽度结论或 (3.1) 直接越界应用。

#### P6.1.triangular

- 类型：`proof_step`；页码：13；定位：Relative to the initial basis ...

**规范**：$k=0$ 时相对于定义 $\Delta$ 的初始基，各有限列变换为上三角。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_star；Delta

**证明路线 / 依赖**：P6.1.finite.zero

#### P6.1.diagonal.C0

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, C0

**规范**：第 $r$ 列对角系数为 $1$，对角乘积为 $1=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_C0；nu_C0

**证明路线 / 依赖**：P6.1.triangular；DEF.V.C0；DEF.nu.zero.C0

#### P6.1.diagonal.BC

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, BC

**规范**：第 $r$ 列对角系数为 $1$，对角乘积为 $1=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_BC；nu_BC

**证明路线 / 依赖**：P6.1.triangular；DEF.V.BC；DEF.nu.zero.BC

#### P6.1.diagonal.B0

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, B0

**规范**：第 $r$ 列对角系数为 $1$，对角乘积为 $1=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_B0；nu_B0

**证明路线 / 依赖**：P6.1.triangular；DEF.V.B0；DEF.nu.zero.B0

#### P6.1.diagonal.Ct

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, Ct

**规范**：第 $r$ 列对角系数为 $1+t^r$，对角乘积为 $(-t;t)_n=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_Ct；nu_Ct

**证明路线 / 依赖**：P6.1.triangular；DEF.V.Ct；DEF.nu.zero.Ct

#### P6.1.diagonal.Bt

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, Bt

**规范**：第 $r$ 列对角系数为 $1+t^r$，对角乘积为 $(-t;t)_n=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_Bt；nu_Bt

**证明路线 / 依赖**：P6.1.triangular；DEF.V.Bt；DEF.nu.zero.Bt

#### P6.1.diagonal.Bminus

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, Bminus

**规范**：第 $r$ 列对角系数为 $1-\tau^{2r-1}$，对角乘积为 $(\tau;\tau^2)_n=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_Bminus；nu_Bminus

**证明路线 / 依赖**：P6.1.triangular；DEF.V.Bminus；DEF.nu.zero.Bminus

#### P6.1.diagonal.Bplus

- 类型：`proof_step`；页码：14；定位：width-zero diagonal table, Bplus

**规范**：第 $r$ 列对角系数为 $1+t^{r-1}$，对角乘积为 $(-1;t)_n=\nu_\star(0)$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$1\le r\le n$

**对象**：V_Bplus；nu_Bplus

**证明路线 / 依赖**：P6.1.triangular；DEF.V.Bplus；DEF.nu.zero.Bplus

**边界与核查义务**：$B_+$ 首系数为 $1+t^0=2$。

#### P6.1.Bt.first

- 类型：`proof_step`；页码：14；定位：For example, the Bt columns ... first

**规范**：$B_t$ 的首列求值是 $(1+t)\psi_1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：V_Bt

**证明路线 / 依赖**：DEF.V.Bt

#### P6.1.Bt.rest

- 类型：`proof_step`；页码：14；定位：For example, the Bt columns ... rest

**规范**：$B_t$ 的第 $r\ge2$ 列为 $(1+t^r)\psi_r-(t+t^{r-1})\psi_{r-1}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$2\le r\le n$

**对象**：V_Bt

**证明路线 / 依赖**：DEF.V.Bt

#### P6.1.BC.first

- 类型：`proof_step`；页码：14；定位：while the BC columns ... first

**规范**：$BC$ 的首列求值是 $\phi_1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$t=\tau^2$

**对象**：V_BC

**证明路线 / 依赖**：DEF.V.BC

#### P6.1.BC.rest

- 类型：`proof_step`；页码：14；定位：while the BC columns ... rest

**规范**：$BC$ 的第 $r\ge2$ 列为 $\phi_r+(\tau-\tau^{2r-1})\phi_{r-1}-\tau^{2r-2}\phi_{r-2}$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$；$t=\tau^2$；$2\le r\le n$

**对象**：V_BC

**证明路线 / 依赖**：DEF.V.BC

**边界与核查义务**：$r=2$ 时 $\phi_0=0$。

#### P6.1.Bplus.center

- 类型：`proof_step`；页码：14；定位：For B+ the first column ...

**规范**：$B_+$ 第一列为 $C_0=2$，相对于 $\chi_1=1$ 的对角系数确为 $2$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：V_Bplus；chi

**证明路线 / 依赖**：DEF.Cfun；DEF.chi；DEF.V.Bplus

#### P6.1.empty.affine

- 类型：`proof_step`；页码：14；定位：last sentence of proof

**规范**：五个没有外部半系数的仿射表达式在 $k=0$ 时由空行列式约定等于 $1$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$；$k=0$

**对象**：J_K

**证明路线 / 依赖**：CONV.empty.det；CONV.empty.vector；CONV.empty.noeval

#### P6.1.rational.cancellation

- 类型：`convention`；页码：14；定位：paragraph beginning These are rational-function identities

**规范**：归一化等式在消去之前是有理函数恒等式；显示归一化因子的所有可去奇点均在消去之后解释。结论不要求每个 Pochhammer 因子在所取数值上非零。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；在系数域 $\mathbb Q(t,x_1,\ldots,x_n)$ 中；$BC,B_-$ 两例改用 $\mathbb Q(\tau,x_1,\ldots,x_n)$ 并令 $t=\tau^2$

**对象**：nu_star；P_star

**证明路线 / 依赖**：DEF.Weyl.sum；P6.1.finite.zero；P6.1.triangular

**边界与核查义务**：不能将 $\nu_\star(0)\ne0$ 的数值条件添加到宽零结论；同样不能在未消去的 $0/0$ 表达式上作值域判断。

### C6.2

#### C6.2.6.1

- 类型：`statement`；页码：14；定位：Corollary 6.2, (6.1) 6.1

**规范**：$\dfrac{\det[\phi_{k+r}(x_a)]}{\Delta_C(x)}=\det[\dot e_{n-i+j}-\dot e_{n+i+j}]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：classical_dual_det

**证明路线 / 依赖**：DEF.phi；DEF.psi；DEF.Cfun；WEYL.delta.C；WEYL.delta.B；WEYL.delta.plus；DEF.Edot；DEF.Eddot

**边界与核查义务**：秩与宽度均正；没有宣称公式中的半系数可原样延至 $k=0$。

#### C6.2.6.2.dot

- 类型：`statement`；页码：14；定位：Corollary 6.2, (6.2) 6.2.dot

**规范**：$\dfrac{\det[\psi_{k+r}(x_a)]}{\Delta_B(x)}=\det[\dot e_{n-i+j}+\dot e_{n+i+j-1}]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：classical_dual_det

**证明路线 / 依赖**：DEF.phi；DEF.psi；DEF.Cfun；WEYL.delta.C；WEYL.delta.B；WEYL.delta.plus；DEF.Edot；DEF.Eddot

**边界与核查义务**：秩与宽度均正；没有宣称公式中的半系数可原样延至 $k=0$。

#### C6.2.6.2.ddot

- 类型：`statement`；页码：14；定位：Corollary 6.2, (6.2) 6.2.ddot

**规范**：$\dfrac{\det[\psi_{k+r}(x_a)]}{\Delta_B(x)}=\tfrac12\det[\ddot e_{n-i+j}+\ddot e_{n+i+j-1}]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：classical_dual_det

**证明路线 / 依赖**：DEF.phi；DEF.psi；DEF.Cfun；WEYL.delta.C；WEYL.delta.B；WEYL.delta.plus；DEF.Edot；DEF.Eddot

**边界与核查义务**：秩与宽度均正；没有宣称公式中的半系数可原样延至 $k=0$。

#### C6.2.6.3

- 类型：`statement`；页码：14；定位：Corollary 6.2, (6.3) 6.3

**规范**：$\dfrac{\det[C_{k+r-1}(x_a)]}{\Delta_+(x)}=\tfrac12\det[\dot e_{n-i+j}+\dot e_{n+i+j-2}]$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：classical_dual_det

**证明路线 / 依赖**：DEF.phi；DEF.psi；DEF.Cfun；WEYL.delta.C；WEYL.delta.B；WEYL.delta.plus；DEF.Edot；DEF.Eddot

**边界与核查义务**：秩与宽度均正；没有宣称公式中的半系数可原样延至 $k=0$。

#### C6.2.specialize.C0

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, C0

**规范**：七例之一 $C0$ 的有限表示在零参数下化为 辛型左端 (6.1)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_C0

**证明路线 / 依赖**：DEF.V.C0；C6.2.columns.zero

#### C6.2.specialize.Ct

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, Ct

**规范**：七例之一 $Ct$ 的有限表示在零参数下化为 辛型左端 (6.1)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_Ct

**证明路线 / 依赖**：DEF.V.Ct；C6.2.columns.zero

#### C6.2.specialize.BC

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, BC

**规范**：七例之一 $BC$ 的有限表示在零参数下化为 辛型左端 (6.1)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_BC

**证明路线 / 依赖**：DEF.V.BC；C6.2.columns.zero

#### C6.2.specialize.B0

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, B0

**规范**：七例之一 $B0$ 的有限表示在零参数下化为 移位正交型左端 (6.2)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_B0

**证明路线 / 依赖**：DEF.V.B0；C6.2.columns.zero

#### C6.2.specialize.Bminus

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, Bminus

**规范**：七例之一 $B_-$ 的有限表示在零参数下化为 移位正交型左端 (6.2)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_Bminus

**证明路线 / 依赖**：DEF.V.Bminus；C6.2.columns.zero

#### C6.2.specialize.Bplus

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, Bplus

**规范**：七例之一 $B_+$ 的有限表示在零参数下化为 对称折叠左端 (6.3)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_Bplus

**证明路线 / 依赖**：DEF.V.Bplus；C6.2.columns.zero

#### C6.2.specialize.Bt

- 类型：`statement`；页码：14；定位：last sentence of Corollary 6.2, Bt

**规范**：七例之一 $Bt$ 的有限表示在零参数下化为 移位正交型左端 (6.2)。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_Bt

**证明路线 / 依赖**：DEF.V.Bt；C6.2.columns.zero

#### C6.2.columns.zero

- 类型：`proof_step`；页码：15；定位：first sentence of proof

**规范**：$t=0$（平方根例同时 $\tau=0$）时，表 1 每个有限列化为 $[k+r]_\diamond$.

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：V_star

**证明路线 / 依赖**：DEF.V.C0；DEF.V.Ct；DEF.V.BC；DEF.V.B0；DEF.V.Bminus；DEF.V.Bplus；DEF.V.Bt

**边界与核查义务**：$u_1$ 原来单独定义；$r\ge2$ 的 $t^{r-1}$ 才严格正幂，不能把第一列套入双项式。

#### C6.2.nonzero.shifts.C0

- 类型：`proof_step`；页码：15；定位：In the affine formulas ... C0

**规范**：$C0$ 的仿射权中每个非零移位 $y\ne0$ 具有严格正参数指数，故零参数特化后仅 $y=0$ 保留。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$；$1\le j\le k$

**对象**：weight_C0

**证明路线 / 依赖**：PARAM.polynomial；A.1.6

**边界与核查义务**：结论只针对这里列出的四例；不能从非负性推成所有七例都严格正。

#### C6.2.nonzero.shifts.B0

- 类型：`proof_step`；页码：15；定位：In the affine formulas ... B0

**规范**：$B0$ 的仿射权中每个非零移位 $y\ne0$ 具有严格正参数指数，故零参数特化后仅 $y=0$ 保留。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$；$1\le j\le k$

**对象**：weight_B0

**证明路线 / 依赖**：PARAM.polynomial；A.1.3

**边界与核查义务**：结论只针对这里列出的四例；不能从非负性推成所有七例都严格正。

#### C6.2.nonzero.shifts.Bplus

- 类型：`proof_step`；页码：15；定位：In the affine formulas ... Bplus

**规范**：$B_+$ 的仿射权中每个非零移位 $y\ne0$ 具有严格正参数指数，故零参数特化后仅 $y=0$ 保留。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$；$1\le j\le k$

**对象**：weight_Bplus

**证明路线 / 依赖**：PARAM.polynomial；A.1.5

**边界与核查义务**：结论只针对这里列出的四例；不能从非负性推成所有七例都严格正。

#### C6.2.nonzero.shifts.Bt

- 类型：`proof_step`；页码：15；定位：In the affine formulas ... Bt

**规范**：$Bt$ 的仿射权中每个非零移位 $y\ne0$ 具有严格正参数指数，故零参数特化后仅 $y=0$ 保留。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$；$1\le j\le k$

**对象**：weight_Bt

**证明路线 / 依赖**：PARAM.polynomial；B.1.9

**边界与核查义务**：结论只针对这里列出的四例；不能从非负性推成所有七例都严格正。

#### C6.2.Ct.exception

- 类型：`proof_step`；页码：15；定位：For Ct one should instead use ...

**规范**：$C_t$ 在 $j=k,y=1$ 时指数 $ky^2-jy=0$，所以非零移位不会逐项全消失。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：Ct_weight

**证明路线 / 依赖**：A.1.7；P5.1.a

**边界与核查义务**：禁止用“$t=0$ 只剩 $y=0$”证明 Ct 特化。

#### C6.2.Ct.parity

- 类型：`proof_step`；页码：15；定位：last sentence of proof

**规范**：$C_t$ 应先取其已证明的有限比值，再由既有奇偶投影恒等式将专化后的偶格和识别为同一个辛型行列式。

**前提**：$n\ge1$；$x_1,\ldots,x_n$ 为形式变量，$x_a^{-1}$ 按有理函数解释；$n,k\ge1$；左端 $1\le a,r\le n$，右端 $1\le i,j\le k$；有理函数比值按消去后解释；$t=0$，平方根例同时 $\tau=0$

**对象**：P_Ct；Z_even

**证明路线 / 依赖**：C6.2.specialize.Ct；P5.1.even.lattice；C6.2.Ct.exception

