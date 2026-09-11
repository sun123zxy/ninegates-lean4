# Ninegates Lean4 非活全面听分类：激进重构规格

## 0. Change overview

This change happens in `ninegates-writeup`'s `casual.qmd` (located at `D:\workspace\ninegates-writeup\ninegates\casual.qmd`) at commit `5eae17812b8f3231b1282bd729b7e569a1629a8e`. Check the commit history for mathematical details.

当前 `ninegates-lean4` 的主结果围绕

```lean
IsLiveFullWait c → c = standardLiveFullWait n
```

组织，整个 `Counterexample` pipeline 也围绕 **live counterexample** 建造。

上述 writeup commit 把数学结果加强为**全部普通全面听的分类**：

* \(n=1\) 时，普通全面听恰有六种，而且六种全部是活全面听；
* \(n\ge2\) 时，普通全面听恰有八族

  $$
  A_n,B_n,B'_n,C_n,C'_n,D_n,D'_n,E_n;
  $$
* \(n\ge2\) 时，这八族中只有 \(A_n\) 是活全面听。

因此 Lean 仓库应进行一次激进重构，使其数学架构直接表达：

```text
全部普通 IsFullWait 的分类
        ↓
n = 1：六个标准解
n ≥ 2：八个标准族
        ↓
对 n ≥ 2 使用 liveness 排除 B/B'/C/C'/D/D'/E
        ↓
A 是唯一活全面听
```

核心原则：

> Counterexample reduction、minimal counterexample、finite candidate enumeration、computational elimination 全部建立在普通 `IsFullWait` 上。
> `IsLiveFullWait` 不参与反例约化，只在标准族自身的 liveness lemma 与最终 live uniqueness corollary 中出现。

不保留旧 API 的 compatibility alias。源码应直接表达新的数学结构。

---

# 1. `Hand.Standard` 成为全部显式标准解的归属

`Ninegates/Standard.lean` 重写为：

```lean
namespace Mahjong.Hand.Standard
```

这里保存：

1. \(n\ge2\) 的八个参数族；
2. \(n=1\) 的六个具体全面听；
3. 每个标准解自己的坐标、size、full-wait、liveness 等基本事实；
4. `insertSeqAt` 的定义、基础引理，以及各标准族的 insertion behavior。

`insertSeqAt` 从 `Ninegates/Counterexample/Reduction.lean` 迁入
`Ninegates/Standard.lean`，保留通用操作的名称 `Mahjong.Hand.insertSeqAt`。
该定义及其基础引理写在 `Mahjong.Hand` namespace 中；标准对象及其专属引理
写在 `Mahjong.Hand.Standard` 及各族 namespace 中。

因此 `Standard.lean` 先提供插入操作，再证明各族的插入性质；
`Counterexample/Reduction.lean` 导入并使用这些结果。
`Standard.lean` 不得反向依赖 `Counterexample`，也不再由 `Counterexample` 提供插入操作。

不要再保留：

```text
standardLiveFullWait
```

所有旧用途直接迁移到 `Standard.A`。

---

# 2. \(n\ge2\) 的八个实际定义

定义：

```lean
def A  (n : ℕ) : Hand n := ...
def B  (n : ℕ) : Hand n := ...
def B' (n : ℕ) : Hand n := ...
def C  (n : ℕ) : Hand n := ...
def C' (n : ℕ) : Hand n := ...
def D  (n : ℕ) : Hand n := ...
def D' (n : ℕ) : Hand n := ...
def E  (n : ℕ) : Hand n := ...
```

对应 writeup：

$$
\begin{aligned}
A_n&=(3,1^{3n-2},3),\\
B_n&=(3,1^{3n-5},4,1,1,0),\\
B'_n&=(0,1,1,4,1^{3n-5},3),\\
C_n&=(1,1,4,1^{3n-5},3,0),\\
C'_n&=(0,3,1^{3n-5},4,1,1),\\
D_n&=(0,1,4,2,1^{3n-6},3,0),\\
D'_n&=(0,3,1^{3n-6},2,4,1,0),\\
E_n&=(0,1,1,4,1^{3n-8},4,1,1,0)
\end{aligned}
$$

其中

$$
E_2=(0,1,4,4,1,0).
$$

`E` 应把 `n = 2` 的特殊情况直接编码进实际定义。

不要为了兼容旧代码给 `A` 再起旧名字。

---

# 3. \(n=1\) 的六个实际定义也放入 `Standard`

writeup 中的六副牌为也放入 standard．具体名字在实现时可以选择简洁且稳定的 scheme，例如根据翻转对称性以小写字母和 `'` 标记．

同样，每个对象自己的 lemma 放入自己的 namespace：

```lean
namespace Mahjong.Hand.Standard.One.a

lemma apply ...
lemma size ...
theorem isFullWait ...
theorem isLiveFullWait ...

end Mahjong.Hand.Standard.One.a
```

不要把 \(n=1\) 当成形式化末尾的临时补丁；它从一开始就是 `Standard` 层的一部分。

---

# 4. Family-specific namespace 规范

每个参数族的引理放在对应 namespace：

```lean
namespace Mahjong.Hand.Standard.A

lemma apply ...
lemma size ...
theorem isFullWait ...
theorem isLiveFullWait ...
theorem insertSeqAt_... ...

end Mahjong.Hand.Standard.A
```

例如：

```lean
namespace Mahjong.Hand.Standard.B

lemma apply ...
lemma size ...
theorem isFullWait ...
theorem not_isLiveFullWait ...
theorem insertSeqAt_... ...

end Mahjong.Hand.Standard.B
```

其它族同理。

使用风格应为：

```lean
Standard.A n
Standard.A.apply
Standard.A.size
Standard.A.isFullWait

Standard.B n
Standard.B.apply
Standard.B.isFullWait
Standard.B.not_isLiveFullWait
```

避免把几十个 family-specific theorem 全部平铺到 `Mahjong.Hand` 或 `Mahjong.Hand.Standard`。

---

# 5. 可以引入 `IsEightFamily`，但只能是浅包装

允许定义：

```lean
abbrev IsEightFamily {n : ℕ} (c : Hand n) : Prop :=
  c = Standard.A n ∨
  c = Standard.B n ∨
  c = Standard.B' n ∨
  c = Standard.C n ∨
  c = Standard.C' n ∨
  c = Standard.D n ∨
  c = Standard.D' n ∨
  c = Standard.E n
```

这是允许且推荐的，因为它只是八个 equality 析取的**浅包装**。

要求：

* 用 `abbrev`，不要制造新的 opaque abstraction；
* downstream 随时可以直接展开成八个 equality；
* 不要围绕它另外建一套复杂 API；
* 八族仍然必须首先是八个真实定义。

它主要用于简化：

```lean
IsCE
fullWait_classification
insertion stability
native_decide certificate
```

等 theorem statement。

类似地，如果 \(n=1\) 六个对象的反复析取造成明显噪音，可以引入一个同样浅的

```lean
abbrev IsOrderOneFamily (c : Hand 1) : Prop := ...
```

但不要让 shallow wrapper 取代实际对象。

这两个浅包装也定义在 `Standard.lean` 中，供标准族插入引理和
`Counterexample.Basic` 共同使用，避免 `Standard` 依赖反例层。

---

# 6. `Standard` 层必须证明的事实

对于八个参数族，至少完成：

```text
coordinate/apply characterization
size
IsFullWait
liveness status
用于 insertion reduction 的 family-specific lemmas
```

具体而言：

```lean
Standard.A.isFullWait
Standard.B.isFullWait
Standard.B'.isFullWait
...
Standard.E.isFullWait
```

以及：

```lean
Standard.A.isLiveFullWait

Standard.B.not_isLiveFullWait
Standard.B'.not_isLiveFullWait
...
Standard.E.not_isLiveFullWait
```

后七个基本都应该通过存在某个 multiplicity \(4\) 的坐标得到。

对于 \(n=1\) 六个对象，全部证明：

```text
IsFullWait
IsLiveFullWait
```

这些都是 classification theorem 反向和最终 theorem 所需的 positive facts。当然，$n$ 固定的情形直接 `native_decide` 应该比较方便。

---

# 7. Counterexample 层只讨论普通 full wait

彻底删除：

```lean
IsLiveCE
HasLiveCE
```

新的 \(n\ge2\) counterexample 定义：

```lean
abbrev IsCE {n : ℕ} (c : Hand n) : Prop :=
  IsFullWait c ∧ ¬ IsEightFamily c

abbrev HasCE (n : ℕ) : Prop :=
  ∃ c : Hand n, IsCE c
```

因为 `IsEightFamily` 是 `abbrev`，这与直接写八个 inequality 没有额外逻辑层。

Counterexample machinery 的主要用途仍是 \(n\ge2\) 的八族分类，因为 `(1,1,1)`-deletion induction 从 \(n\ge3\) 向下最终落在 \(n=2\)。

\(n=1\) 不需要参与该 inductive reduction，但它**必须进入统一 finite candidate enumeration infrastructure**，见后文。

---

# 8. 主结果目标

## \(n\ge2\)

核心 classification：

```lean
theorem fullWait_classification
    (n : ℕ) (hn : 2 ≤ n)
    (c : Hand n) (hc : IsFullWait c) :
    IsEightFamily c
```

因为 `IsEightFamily` 是浅 `abbrev`，用户展开后立即得到：

```text
c = A n ∨ c = B n ∨ ... ∨ c = E n
```

再提供 iff：

```lean
theorem isFullWait_iff_eightFamily
    (n : ℕ) (hn : 2 ≤ n) (c : Hand n) :
    IsFullWait c ↔ IsEightFamily c
```

反向逐个调用 `Standard.*.isFullWait`。

## \(n=1\)

另外得到：

```lean
theorem orderOne_fullWait_classification
    (c : Hand 1) (hc : IsFullWait c) :
    IsOrderOneFamily c
```

以及对应 iff。

但这里的**枚举算法本身不能另造一套**；它应和 \(n=2\) 共享同一个 small-order branch。

---

# 9. Stage 1 — 激进重写 `Standard.lean`

首先完成所有显式标准对象：

```text
A, B, B', C, C', D, D', E
六个 n=1 标准解
```

旧：

```text
standardLiveFullWait
standardLiveFullWait_apply
size_standardLiveFullWait
IsFullWait.standardLiveFullWait
IsLiveFullWait.standardLiveFullWait
```

全部删除并迁移成：

```text
Standard.A
Standard.A.apply
Standard.A.size
Standard.A.isFullWait
Standard.A.isLiveFullWait
```

不留 alias。

然后完成其它七族和六个 order-one 对象的 trivial structural lemmas。

同时将 `insertSeqAt` 的定义及其基础引理迁入 `Standard.lean`，
包括坐标、size、索引对应和 `insertSeqAt_add_single` 等与插入操作直接相关的事实。
本阶段完成迁移并更新下游引用；八族 insertion behavior 在 Stage 3 完成。

特别注意 automation policy，适当给 `@[grind]` 和 `@[simp]`；

**Stage 1 验收：**

* 所有标准对象已经存在；
* 所有对象已证明真正 `IsFullWait`；
* liveness status 已证明；
* `insertSeqAt` 及其基础引理由 `Standard.lean` 提供；
* `lake build` 通过。

---

# 10. Stage 2 — 重写 Counterexample basic layer

`Counterexample/Basic.lean` 改为普通：

```lean
IsCE
HasCE
```

并引入/使用 shallow：

```lean
IsEightFamily
```

从这个阶段开始，全仓库逐步删除：

```text
IsLiveCE
HasLiveCE
standardLiveFullWait
```

最终零残留。

---

# 11. Stage 3 — `(1,1,1)` deletion / insertion 重构

本阶段有两部分：`Standard.lean` 提供八族 insertion behavior，
`Counterexample/Reduction.lean` 使用这些结果完成普通反例的删除约化。

`insertSeqAt` 及其基础引理已在 Stage 1 迁入 `Standard.lean`。
以下删除操作、ordinary deletion lemmas 和大阶数分解定理继续放在
`Counterexample/Reduction.lean`，应尽量直接复用：

```lean
removeSeqAt
HasSeqAt

Meldable.of_insertSeqAt
Winning.of_insertSeqAt
IsFullWait.of_insertSeqAt
exists_insertSeqAt_of_large
```

删除只服务旧 live pipeline 的：

```text
IsLiveFullWait.of_insertSeqAt
Counterexample.IsLiveCE_of_insertSeqAt
liveFullWait_reduction
insertSeqAt_standardLiveFullWait
```

核心新增是八族 insertion behavior。

这些事实写在 `Standard.lean` 中的：

```text
Standard.A
Standard.B
...
Standard.E
```

各自 namespace 内。

数学目标对应 writeup commit：

* \(A_n\)：内部允许位置插入 `111` 后为 \(A_{n+1}\)；
* \(B_n,B'_n,C_n,C'_n,D_n,D'_n,E_n\)：在列出的合法位置插入后得到同族下一阶；
* 未列出的 insertion position 若插入后仍声称是全面听，则导出矛盾；
* \(E_2\) 插入任何位置都不能得到全面听。

可以在这些 family-specific lemmas 之上增加一个浅的汇总 theorem：

```lean
theorem Standard.IsEightFamily.insertSeqAt
    (hc : IsEightFamily c)
    (hfull : IsFullWait (c.insertSeqAt k)) :
    IsEightFamily (c.insertSeqAt k)
```

名称可以调整，但不要为此创造更深的 abstraction。

然后证明：

```lean
lemma Counterexample.IsCE_of_insertSeqAt
    {c : Hand n}
    (k : Fin (3 * n))
    (hk : 0 < k.val)
    (hc : IsCE (c.insertSeqAt k)) :
    IsCE c
```

逻辑：

```text
enlarged CE
→ enlarged full wait
→ deletion gives reduced full wait
→ 若 reduced 是八族
→ family insertion theorem 说明 enlarged 也是八族
→ contradiction
```

最后得到：

```lean
theorem fullWait_reduction
    {n : ℕ} (hn : 2 ≤ n)
    {c : Hand n} (hc : IsCE c) :
    ∃ m, 2 ≤ m ∧ m ≤ 7 ∧ HasCE m
```

该 theorem 完全不提 liveness。

---

# 12. Stage 4 — finite candidate enumeration 统一包含 \(n=1\)

这一部分应按三种数学区间理解：

```text
n = 1
n = 2
3 ≤ n ≤ 7
```

但**枚举算法层面 \(n=1\) 和 \(n=2\) 使用完全相同的 branch**。

原因是这两个阶数都不需要“No interior `111`”这个 minimality restriction。

因此不要：

```text
写一个 n=1 enumerator
再写一个 n=2 enumerator
```

而应共享例如：

```lean
def smallOrderCandidateExcesses (n : Nat) : List (List Nat) :=
  boundedLists (List.replicate (3 * n) 6) 6
```

或者更自然的等价写法。

因为全局 `sum = 6` 已经自动限制每个 coordinate \(\le6\)，无需单独 bounds。

于是：

```text
n = 1 → weak compositions of 6 into 3 positions → 28
n = 2 → weak compositions of 6 into 6 positions → 462
```

使用同一算法。

---

# 13. 新 candidate excess 条件

普通 full wait 已有：

```text
内部正性
excess sum = 6
```

对于 \(n\ge3\) 的 minimal counterexample，额外有：

```text
no interior triple ones
```

对应 excess：

```text
NoTripleZeros interior
```

所以新的 `IsCandidateExcess` 应大致为：

```lean
def IsCandidateExcess (n : Nat) (excess : List Nat) : Prop :=
  ∃ left interior right,
    excess = left :: interior ++ [right] ∧
    interior.length = 3 * n - 2 ∧
    excess.sum = 6 ∧
    (n ≤ 2 ∨ NoTripleZeros interior)
```

若为了 theorem proof 更方便，也可以把 `n = 1 ∨ n = 2` 写显式，但算法上仍然必须共享。

删除旧限制：

```text
left ≤ 3
right ≤ 3
∀ value ∈ interior, value ≤ 2
```

它们全部来自 liveness，不应残留。

---

# 14. `MinimalCandidateExcesses` 的目标结构

推荐整体写成：

```lean
def MinimalCandidateExcesses (n : Nat) : List (List Nat) :=
  if 1 ≤ n && n ≤ 2 then
    smallOrderCandidateExcesses n
  else if 3 ≤ n && n ≤ 7 then
    largeCandidateExcesses n
  else
    []
```

具体 Boolean syntax 可调整。

重要的是概念结构：

```text
1 ≤ n ≤ 2 : 同一 weak-composition enumerator
3 ≤ n ≤ 7 : positive-excess + bounded-zero-gap enumerator
otherwise   : []
```

对应候选数 regression checks：

$$
\begin{array}{c|rrrrrrr}
n&1&2&3&4&5&6&7\\
\hline
\#&28&462&1554&2128&1128&203&7
\end{array}
$$

这些数字应在 Lean 中实际计算验证。

---

# 15. \(3\le n\le7\) 的 large enumerator

现有“positive excess entries + zero gaps”结构可以保留。

新的区别：

旧版本将 positive excess 限制为小值，因为 `c_i ≤ 3`。

现在不应有逐点上界。

只需：

* positive entries 真正 \(>0\)；
* 总 excess 为 \(6\)；
* zero gaps 每段长度 \(\le2\)。

因此 `positiveExcess` 本身应枚举一个总和受 \(6\) 限制的正整数 composition，而不是每项 `≤ 2` 的 bounded list。

两个 boundary excess 同样没有人为的 `≤3` bound；全局 sum \(6\) 已经足够保证有限。

---

# 16. Stage 5 — 重写 EnumSpec soundness/completeness

同步重写：

```text
small-order enumeration specification
largeCandidateExcesses_sound
largeCandidateExcesses_complete
mem_minimalCandidateExcesses_iff
handOfExcess...
IsCandidateExcess.isMinimalCandidate_handOfExcess
IsMinimalCandidate.isCandidateExcess_excessOf
mem_minimalCandidates_iff
```

新的 `IsMinimalCandidate` 应覆盖 \(1\le n\le7\)：

```lean
def IsMinimalCandidate {n : Nat} (c : Hand n) : Prop :=
  1 ≤ n ∧
  n ≤ 7 ∧
  (∀ i : Fin (3 * n - 2),
      1 ≤ c ⟨i.val + 1, by omega⟩) ∧
  Hand.size c = 3 * n + 4 ∧
  (n ≤ 2 ∨ NoInteriorTripleOnes c)
```

这里“minimal”对于 \(n=1\) 在严格反例意义上并不是 reduction chain 的 minimal CE 条件；它更准确地说是 finite-classification candidate condition。若因此觉得命名误导，可以趁激进重构改成更中性的：

```text
IsFiniteCandidate
CandidateExcesses
Candidates
```

这是值得考虑的，因为现在枚举基础设施同时服务：

* \(n=1\) 六解直接分类；
* \(n\ge2\) minimal counterexample elimination。

不要为了保留旧命名而让数学含义变得奇怪。

本阶段还需在 Lean 中实际验证 §27 的候选数：
`28, 462, 1554, 2128, 1128, 203, 7`。

---

# 17. Stage 6 — \(n\ge2\) minimal CE 进入统一 Candidates

对 \(n\ge2\)，重写当前：

```lean
mem_minimalCandidates_of_minimal
```

输入：

```lean
hn : 2 ≤ n
hc : IsCE c
hmin : ∀ m, 2 ≤ m → m < n → ¬ HasCE m
```

证明：

1. `hc.1 : IsFullWait c`;
2. `interior_positive`;
3. `IsFullWait.size`;
4. `fullWait_reduction` 得 \(n\le7\);
5. 若 \(n\ge3\) 且内部有 `111`，由 `IsCE_of_insertSeqAt` 得更低阶 CE，违反 minimality；
6. 因此 `c ∈ Candidates n`。

这里不出现任何：

```text
IsLiveFullWait.le_three
isLiveFullWait_iff_le_three
```

---

# 18. Stage 7 — finite elimination 同时服务 \(n=1\) 与 \(n\ge2\)

计算 certificate 应基于统一的 `Candidates n`。

## 对 \(n\ge2\)

证明：

```lean
theorem candidates_no_CE
    (n : Nat) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    ∀ c ∈ Candidates n, ¬ IsCE c
```

检查：

```text
如果 candidate 是 IsFullWait
那么 IsEightFamily candidate
```

## 对 \(n=1\)

用**同一个 `Candidates 1`**，证明：

```lean
theorem orderOne_candidates_classified :
    ∀ c ∈ Candidates 1,
      IsFullWait c → IsOrderOneFamily c
```

或者直接用对应 decidable proposition 做 `native_decide` certificate。

关键要求：

> \(n=1\) 可以有独立的 classification theorem / certificate statement，但不能有独立的 enumeration algorithm。

底层枚举必须与 \(n=2\) 共用 small-order enumerator。

---

# 19. Stage 8 — \(n\ge2\) 主 classification

证明：

```lean
theorem fullWait_classification
    (n : ℕ) (hn : 2 ≤ n)
    (c : Hand n) (hc : IsFullWait c) :
    IsEightFamily c
```

仍采用 minimal CE contradiction：

```text
假设 ¬ IsEightFamily c
→ IsCE c
→ 构造 HasCE n
→ Nat.find 取 minimal order m
→ minimal CE d
→ d ∈ Candidates m
→ finite certificate says ¬ IsCE d
→ contradiction
```

然后：

```lean
theorem isFullWait_iff_eightFamily
    (n : ℕ) (hn : 2 ≤ n) (c : Hand n) :
    IsFullWait c ↔ IsEightFamily c
```

---

# 20. Stage 8 — \(n=1\) classification

这里不再需要任何新的 enumerator。

直接基于：

```text
Candidates 1
```

的 28 个 weak-composition candidates 与 Stage 7 certificate 得到：

```lean
theorem orderOne_fullWait_classification
    (c : Hand 1) (hc : IsFullWait c) :
    IsOrderOneFamily c
```

并进一步：

```lean
theorem orderOne_isFullWait_iff_standard ...
```

反向调用六个 `Standard.One*.isFullWait`。

因此 \(n=1\) 是**classification theorem 单独陈述，enumeration infrastructure 不单独实现**。

---

# 21. Stage 9 — liveness 最后过滤

最终：

```lean
theorem liveFullWait_unique
    (n : ℕ) (hn : 2 ≤ n)
    (c : Hand n) (hc : IsLiveFullWait c) :
    c = Standard.A n
```

证明必须非常短：

```text
hc
→ ordinary IsFullWait
→ fullWait_classification
→ IsEightFamily cases
→ A 留下
→ B...E 分别与 Standard.*.not_isLiveFullWait 矛盾
```

这里不再：

* 构造 counterexample；
* 使用 minimality；
* 调用 reduction；
* 调用 native_decide。

Live uniqueness 只是 classification 的 corollary。

对于 \(n=1\)，六个标准解全部 `IsLiveFullWait`，无需唯一性陈述。

---

# 22. 建议的最终 theorem 层级

最终公开数学结果应大致形成：

```text
Standard.A ... E

orderOne_fullWait_classification
orderOne_isFullWait_iff_standard

fullWait_classification          -- n ≥ 2
isFullWait_iff_eightFamily       -- n ≥ 2

liveFullWait_unique              -- n ≥ 2
```

这样顶层结构直接对应 writeup 的主定理。

---

# 23. Stage 10 — 全仓库清理与最终验证

最终仓库中不应残留：

```text
standardLiveFullWait

IsLiveCE
HasLiveCE

Counterexample.IsLiveCE_of_insertSeqAt
liveFullWait_reduction
minimalCandidates_no_liveCE

IsMinimalCandidate 中的 ∀ i, c i ≤ 3

IsCandidateExcess 中的
  left ≤ 3
  right ≤ 3
  interior value ≤ 2

所有 “minimal live counterexample”
“live counterexample candidates”
等旧 docstring
```

允许增加：

```text
IsEightFamily
IsOrderOneFamily
```

但必须是 `abbrev` 型浅包装，不能替代实际标准解定义。

同步更新 module docstrings，使其描述普通全面听分类及最终的 live corollary。
README 由仓库作者负责更新，代理不得修改；更新 README 不属于代理的执行或验收任务。
检查 imports，特别是 `Standard` 提供插入操作、`Counterexample.Reduction` 使用它的依赖方向。
最后运行 `lake build`，并检查主要 theorem 的 axioms。

---

# 24. 尽量不动的底层模块

除非证明过程中发现必要，不重构：

```text
Hand 的基本表示
Meldable 核心结构
Winning 核心结构
Wait predicates
Winning / Wait decision algorithms
Positivity 主结果
```

已有以下 theorem 正好适合新 proof：

```lean
IsFullWait
IsFullWait.size

interior_positive
excess_eq_six
interior_excess_le_six

Meldable.of_insertSeqAt
Winning.of_insertSeqAt
IsFullWait.of_insertSeqAt
exists_insertSeqAt_of_large
```

优先复用。

---

# 25. 目标依赖图

最终结构应接近：

```text
Basic / Meldable / Winning / Wait
              │
        ┌─────┴─────┐
        ▼           ▼
   Positivity   Hand.Standard
                │
                ├─ insertSeqAt + 基础引理
                │
                ├─ OneA ... OneF
                │
                └─ A B B' C C' D D' E
                   + 各族 insertion behavior
        │           │
        └─────┬─────┘
              ▼
      Counterexample.Basic
              │
              ▼
      Counterexample.Reduction
              │
              ▼
         Candidate Enum
       ┌──────┴────────┐
       │               │
  n = 1,2 shared    3 ≤ n ≤ 7
  weak composition   gap-based
       │               │
       └──────┬────────┘
              ▼
          EnumSpec
              │
              ▼
         Elimination
          │        │
          ▼        ▼
       n = 1     n ≥ 2
      six-way    eight-way
   classification classification
                     │
                     ▼
            liveFullWait_unique
```

最重要的架构限制仍然是：

```text
Counterexample reduction
        ↓
ordinary IsFullWait only
```

liveness 不能重新渗透进这一条链。

---

# 26. 统一执行阶段索引

全文使用以下唯一一套 Stage 1–10 编号。表中引用的章节给出详细要求；
§19 和 §20 同属 Stage 8，分别陈述两个阶数范围的 classification。

| Stage | 工作与验收范围 | 详细规格 |
|---|---|---|
| 1 | 重写 `Standard.lean`：八族、六个一阶解、各自的坐标 / size / full-wait / liveness；迁入 `insertSeqAt` 及基础引理，更新下游引用，通过 `lake build` | §9 |
| 2 | 使用 `Standard` 的浅包装，重写 `Counterexample.Basic` 为普通 `IsCE` / `HasCE`，开始清除 live CE API | §10 |
| 3 | 在 `Standard.lean` 证明各族及 `IsEightFamily` 的插入性质；在 `Counterexample.Reduction` 复用 ordinary deletion，证明 `IsCE_of_insertSeqAt` 和 `fullWait_reduction` | §11 |
| 4 | 重写枚举：`n=1,2` 共用 weak-composition branch，`3≤n≤7` 使用 gap branch，删除 live upper bounds | §12–15 |
| 5 | 重写 EnumSpec：candidate characterization、soundness/completeness，统一覆盖 `1≤n≤7`，实际验证七个候选数 | §16、§27 |
| 6 | 证明 `n≥2` 的 minimal CE 必在统一 `Candidates` 中 | §17 |
| 7 | 计算消除：`Candidates 1` 中的全面听属于六个标准解；`Candidates 2` 至 `Candidates 7` 中的全面听属于八族 | §18 |
| 8 | 证明 `orderOne_fullWait_classification`、`fullWait_classification` 及两个 iff theorem | §19–20 |
| 9 | 由分类与各族 liveness 推出 `liveFullWait_unique` | §21 |
| 10 | 清除旧命名，更新 module docstrings，检查 imports，通过 `lake build` 并检查主要 theorem axioms；README 由作者负责，代理不得修改 | §23 |

---

# 27. Enumeration regression checks

这次重构改变枚举空间，因此以下数字属于重要 correctness guard：

$$
\begin{array}{c|rrrrrrr}
n&1&2&3&4&5&6&7\\
\hline
\#\text{candidates}
&28&462&1554&2128&1128&203&7
\end{array}
$$

特别注意：

* \(n=1\) 与 \(n=2\) 必须来自同一个枚举函数；
* 两者只因 `3*n` 不同而分别产生 28 和 462；
* 从 \(n=3\) 开始才启用 `NoTripleZeros` / no-`111` 结构压缩。

如果实际 candidate counts 不符，应先认为 enumerator/spec 有问题，而不是修改预期数字。

---

# 28. 最终验收标准

完成后代码库应直接表达：

```text
Standard
= 所有已知显式 full-wait 解 + insertSeqAt 及各族插入性质

n = 1
= 六个标准解，全部 live

n ≥ 2
= 八个参数族

Counterexample
= 八族之外的普通 full wait

Reduction
= 普通 CE 的 (1,1,1)-删除

Enumeration
= n=1,2 的统一 weak-composition branch
  + 3≤n≤7 的 gap branch

Elimination
= 有限验证无遗漏

Classification
= 全部普通全面听的完整分类

Liveness
= 分类完成后的最终筛选
```

仓库的核心数学叙事应变成：

> 首先分类所有允许空听的全面听；纯正 \(3n\) 莲宝灯 \(A_n\) 的活唯一性随后立即得到。

而不应再残留旧架构：

> 先围绕 live counterexample 证明唯一性，再把普通 full wait 当作未来工作。
