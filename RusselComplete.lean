import RusselComplete.Basic

import Mathlib

namespace RusselComplete
/-
两个目标：
1. 证明罗素公理的完备性：说明rw和intro这两个推理规则可以用罗素公理说明
2. 实现lean4文件到markdown的自动转换，并且markdown文件符合严谨性
这份代码旨在实现第一个目标
成果见文件末尾，前面的部分是已证明的各种定理
-/

-- 公理
axiom A1 (P : Prop) : ((P ∨ P) → P)
axiom A2 (P Q : Prop) : (P → (P ∨ Q))
axiom A3 (P Q : Prop) : ((P ∨ Q) → (Q ∨ P))
axiom A4 (P Q R : Prop) : ((Q → R) → ((P ∨ Q) → (P ∨ R)))
-- 定义
axiom D1 (A B : Prop) : ((A → B) = (¬A ∨ B))
axiom D2 (A B : Prop) : ((A ∧ B) = ¬(¬A ∨ ¬B))
axiom D3 (A B : Prop) : ((A ↔ B) = ((A → B) ∧ (B → A)))

/-
对于lean4语法与罗素公理的等效以及lean4转换markdown的思考
只要满足以下规则，那么它就是有等价的罗素公理的证明的

2025.10.16 细化推理规则，用于 lean4 自动生成 markdown 的证明
正向工程：
1.  带入规则：就是函数带入，定理名 变量1 变量2 ……
2.  分离规则：exact (α → β) α ，其中两项内容都已经证明，α和β是两个式子
3.  置换规则：rw[D1/D2/D3]，只能是这三项，然后可以应用@号来指定重写
4.  have, 说明一个步骤, 后面使用一行by+以上规则来证明这个步骤
    特别的，一条定理结束的不用by
5.  exact 最后一个have的名字 ，这一步在markdown中是省略的
逆向工程：
5.  分离规则：apply (α → goal) ，将goal转变为α
    实际上等价于在最后加入 exact (α → goal) α
6.  置换规则：rw[...]
    等价于在最后加入这一行内容：
    have ha : goal := by rw[...] at hb; exact hb
为了逆向工程的衔接，我们将证明最后一步的 exact goal 去掉，改为：当goal与某一个子命题完全相同时结束
某些“不规范”写法：
7.  直接使用 rw[...] at h
    等价于用相同名字的另一条式子覆盖了这一条
8.  分离规则的exact中，(α → β)与α均可以是带入规则的结果
    等价于：先将带入规则得到的式子全写下来，然后分离
9.  多步分离：exact (α → (β → γ)) α β
    等价于：每一步分离结果都写下来，之后都在这个结果的基础上搞

2025.10.23
10. 在定理中包含前提，此定理相当于一个推导过程
    这个写法其实与intro是一样的，但是：intro不符合罗素公理中的推理规则，而这么写符合

markdown改写的难点：
1.  如果只有正向规则，可以直接逐文字处理翻译
2.  加入7也不难，这和have操作一样
3.  加入逆向工程和8,9是最难的，需要我解析(α → β)并推断goal的式子
4.  以及，第6条需要我实现rw
-/

-- start

theorem Chain (P Q R : Prop) : ((Q → R) → ((P → Q) → (P → R))) := by
  rw[@D1 P Q]; rw[@D1 P R]
  exact A4 (¬P) Q R

theorem Imp_self (P : Prop) : (P → P) := by
  let v1 := (P ∨ P)
  exact (Chain P v1 P) (A1 P) (A2 P P)

theorem Not_or (P : Prop) : (¬P ∨ P) := by
  let s1 := Imp_self P
  rw[D1] at s1
  exact s1

theorem Or_not (P : Prop) : (P ∨ ¬P) := by
  exact (A3 (¬P) P) (Not_or P)

theorem Not2_r (P : Prop) : (P → ¬¬P) := by
  rw[D1]
  exact Or_not (¬P)

theorem A2_Comm (P Q : Prop) : (P → (Q ∨ P)) := by
  let v1 := (P ∨ Q)
  let v2 := (Q ∨ P)
  exact (Chain P v1 v2) (A3 P Q) (A2 P Q)

theorem Imp_imp (P Q : Prop) : (Q → (P → Q)) := by
  rw[@D1 P Q]
  exact A2_Comm Q (¬P)

theorem Morgan_or (P Q : Prop) : ((¬P ∨ ¬Q) → ¬(P ∧ Q)) := by
  rw[D2]
  exact Not2_r (¬P ∨ ¬Q)

theorem Not2_l (P : Prop) : (¬¬P → P) := by
  rw[D1]
  apply A3
  have h1 : (P ∨ ¬P) := Or_not P
  have h2 : (P ∨ ¬P) → (P ∨ ¬¬¬P) := (A4 P (¬P) (¬¬¬P)) (Not2_r ¬P)
  exact h2 h1

theorem Morgan_and (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
  rw[D2]
  exact Not2_l (¬P ∨ ¬Q)

-- 思考题
-- 引理：在not里面用交换律，体现一种“交换律的置换规则”
-- 这实际上就是一种rw，用后面的完备性证明这个东西会清晰很多
theorem Not_or_comm (P Q : Prop) : (¬(P ∨ Q) → ¬(Q ∨ P)) := by
  rw[D1]
  apply A3
  let v1 := ¬(Q ∨ P)
  let v2 := (Q ∨ P)
  let v3 := (P ∨ Q)
  let v4 := ¬¬(P ∨ Q)
  have h1 : v1 ∨ v2 := Not_or (Q ∨ P)
  have h2 : v1 ∨ v3 := (A4 v1 v2 v3) (A3 Q P) h1
  exact (A4 v1 v3 v4) (Not2_r v3) h2

-- 2025.10.23
-- 引理：更强的A4
-- 这个写法其实相当于过程，也符合罗素公理
theorem Imp_or_lr (P Q R S : Prop) (h1 : P → R) (h2 : Q → S) : (P ∨ Q) → (R ∨ S) := by
  let v1 := P ∨ Q
  let v2 := P ∨ S
  let v3 := S ∨ P
  let v4 := S ∨ R
  let v5 := R ∨ S
  have h3 : v1 → v2 := (A4 P Q S) h2
  have h4 : v1 → v3 := (Chain v1 v2 v3) (A3 P S) h3
  have h5 : v1 → v4 := (Chain v1 v3 v4) (A4 S P R h1) h4
  exact (Chain v1 v4 v5) (A3 S R) h5

-- 2025.10.23
-- 引理：用来在特殊情况下消去∨两边的某一项
theorem Imp_or_dec (P Q : Prop) : ((P → Q) → ((P ∨ Q) → Q)) := by
  have t1_1 : ((P → Q) → ((Q ∨ P) → (Q ∨ Q))) := (A4 Q P Q)
  have t1_2 : (((Q ∨ P) → (Q ∨ Q)) → ((P ∨ Q) → Q)) := by
    rw[@D1 (Q ∨ P) (Q ∨ Q)]
    rw[@D1 (P ∨ Q) Q]
    -- goal: (¬(Q ∨ P) ∨ (Q ∨ Q)) → (¬(P ∨ Q) ∨ Q)
    -- 用let化简：
    let v1 := (Q ∨ Q)
    let v2 := ¬(Q ∨ P)
    let v3 := ¬(P ∨ Q)
    -- 使用引理化简
    exact (Imp_or_lr v2 v1 v3 Q) (Not_or_comm Q P) (A1 Q)
  exact (Chain (P → Q) ((Q ∨ P) → (Q ∨ Q)) ((P ∨ Q) → Q)) t1_2 t1_1

-- 结合律，使用let化简
theorem Or_assoc (P Q R : Prop) : ((P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R)) := by
  have h1 : (Q → (P ∨ Q)) := by
    exact A2_Comm Q P
  -- 应用 A2 转换括号
  have h2 : ((Q ∨ R) → ((P ∨ Q) ∨ R)) := by
    let v1 := Q ∨ R
    let v2 := R ∨ Q
    let v3 := R ∨ (P ∨ Q)
    let v4 := (P ∨ Q) ∨ R
    have h1 : v1 → v3 := (Chain v1 v2 v3) (A4 R Q (P ∨ Q) h1) (A3 Q R)
    exact (Chain v1 v3 v4) (A3 R (P ∨ Q)) h1
  -- 现在出现了要证明的式子，但是多了个 P
  let v31 := P ∨ (Q ∨ R)
  let v32 := P ∨ ((P ∨ Q) ∨ R)
  have h3 : v31 → v32 := by
    exact (A4 P (Q ∨ R) ((P ∨ Q) ∨ R)) h2
  -- 多了个 P 为什么能消去？因为 右边那一堆比P更容易满足
  let v41 := (P ∨ Q)
  let v42 := v41 ∨ R
  have h4 : (P → v42) := (Chain P v41 v42) (A2 v41 R) (A2 P Q)
  exact (Chain v31 v32 v42) (Imp_or_dec P v42 h4) h3

-- 三段论
example (P Q R : Prop) : (((P → Q) ∧ (Q → R)) → (P → R)) := by
  rw[D1]
  rw[D2]
  -- 问题1：P = ¬¬P 在这里面不可以用，因为不满足置换规则：只有定义可以置换
  -- 解决：A4
  -- 问题2：A4 替换的是 ∨ 右边项，我需要替换左边项
  -- 解决：apply A3 交换到右边，最后 apply A3 交换回来
  -- goal: ¬¬(¬(P → Q) ∨ ¬(Q → R)) ∨ (P → R)
  apply A3
  -- 使用 Not2_r 以及 A4 换掉
  have h1 : (((P → R) ∨ (¬(P → Q) ∨ ¬(Q → R))) → ((P → R) ∨ ¬¬(¬(P → Q) ∨ ¬(Q → R)))) := by
    exact (A4 (P → R) (¬(P → Q) ∨ ¬(Q → R)) ¬¬(¬(P → Q) ∨ ¬(Q → R))) (Not2_r (¬(P → Q) ∨ ¬(Q → R)))
  apply h1
  -- goal: (P → R) ∨ (¬(P → Q) ∨ ¬(Q → R))
  -- 希望后面交换
  have h2 : (((P → R) ∨ (¬(Q → R) ∨ ¬(P → Q))) → ((P → R) ∨ (¬(P → Q) ∨ ¬(Q → R)))) := by
    exact (A4 (P → R) (¬(Q → R) ∨ ¬(P → Q)) (¬(P → Q) ∨ ¬(Q → R))) (A3 (¬(Q → R)) (¬(P → Q)))
  apply h2
  -- goal: (P → R) ∨ (¬(Q → R) ∨ ¬(P → Q))
  apply A3
  apply Or_assoc
  rw[← D1]
  rw[← D1]
  exact (Chain P Q R)

-- 完备性论证

-- 证明rw策略是罗素公理范围内的
-- 引入新记号“=”，有如下规则
axiom D_eq (A B : Prop) : (A = B) = ((A → B) ∧ (B → A))
-- axiom Eq_comm(A B : Prop) : (A = B) = (B = A)
-- 这里∧是想说：A=B时，A→B且B→A，不是指罗素公理中的∧，类似于王皓算法里的","
-- 例如这样
theorem Rw_or_comm (P Q : Prop) : (P ∨ Q) = (Q ∨ P) := by
  rw[D_eq]
  constructor
  · exact A3 P Q
  · exact A3 Q P

-- 需要说明两个基本运算的等价性: not和or
-- 都不太难证

-- 引理：逆否命题
theorem Conv_neg (P Q : Prop) : ((P → Q) → ((¬Q) → (¬P))) := by
  rw[@D1 P Q]
  rw[@D1 (¬Q) (¬P)]
  let s1 := A4 (¬P) Q (¬¬Q) (Not2_r Q)
  let s2 := A3 (¬P) (¬¬Q)
  exact Chain (¬P ∨ Q) (¬P ∨ ¬¬Q) (¬¬Q ∨ ¬P) s2 s1

/- 下列定理命名方式：
Rw0表示用于rw的基本单元，有前提
Rw表示可以直接使用的rw定理，不需要前提
-/

theorem Rw0_not (P Q : Prop) (h1 : P = Q) : (¬P) = (¬Q) := by
  rw[D_eq]
  rw[D_eq] at h1
  constructor
  · exact Conv_neg Q P h1.2
  · exact Conv_neg P Q h1.1

theorem Rw0_or_r (P Q R : Prop) (h1 : P = Q) : (R ∨ P) = (R ∨ Q) := by
  rw[D_eq]
  rw[D_eq] at h1
  constructor
  · exact (A4 R P Q) h1.1
  · exact (A4 R Q P) h1.2

theorem Rw0_or_l (P Q R : Prop) (h1 : P = Q) : (P ∨ R) = (Q ∨ R) := by
  let s1 := Rw0_or_r P Q R h1
  rw[D_eq] at s1
  rw[D_eq]
  constructor
  · let s2 := A3 P R
    let s3 := s1.1
    let s4 := A3 R Q
    let s23 := Chain (P ∨ R) (R ∨ P) (R ∨ Q) s3 s2
    let s234 := Chain (P ∨ R) (R ∨ Q) (Q ∨ R) s4 s23
    exact s234
  · let s2 := A3 Q R
    let s3 := s1.2
    let s4 := A3 R P
    let s23 := Chain (Q ∨ R) (R ∨ Q) (R ∨ P) s3 s2
    let s234 := Chain (Q ∨ R) (R ∨ P) (P ∨ R) s4 s23
    exact s234

-- 由此可以说明其他运算的等价性（作为rw方法的演示）
theorem Rw0_imp_l (P Q R : Prop) (h1 : P = Q) : (P → R) = (Q → R) := by
  rw[D1]; rw[D1]
  -- 按表达式树
  let s1 := Rw0_not P Q h1
  let s2 := Rw0_or_l (¬P) (¬Q) R s1
  exact s2

theorem Rw0_imp_r (P Q R : Prop) (h1 : P = Q) : (R → P) = (R → Q) := by
  rw[D1]; rw[D1]
  let s1 := Rw0_or_r P Q (¬R) h1
  exact s1

-- rw演示，在A4上rw交换律
theorem A4_comm (P Q R : Prop) : (Q → R) → ((Q ∨ P) → (R ∨ P)) := by
  -- 目标：rw到 (Q → R) → ((P ∨ Q) → (P ∨ R))
  -- 第一个rw：将 Q ∨ P rw为 P ∨ Q
  -- rw方法：表达式树上，从rw的那个子树开始向上跳
  have rw1 : ((Q → R) → ((Q ∨ P) → (R ∨ P))) = ((Q → R) → ((P ∨ Q) → (R ∨ P))) := by
    let s1 := Rw_or_comm Q P
    let s2 := Rw0_imp_l (Q ∨ P) (P ∨ Q) (R ∨ P) s1
    let s3 := Rw0_imp_r ((Q ∨ P) → (R ∨ P)) ((P ∨ Q) → (R ∨ P)) (Q → R) s2
    exact s3
  -- 第二个rw：将 R ∨ P rw为 P ∨ R
  have rw2 : ((Q → R) → ((P ∨ Q) → (R ∨ P))) = ((Q → R) → ((P ∨ Q) → (P ∨ R))) := by
    let s1 := Rw_or_comm R P
    let s2 := Rw0_imp_r (R ∨ P) (P ∨ R) (P ∨ Q) s1
    let s3 := Rw0_imp_r ((P ∨ Q) → (R ∨ P)) ((P ∨ Q) → (P ∨ R)) (Q → R) s2
    exact s3
  rw[D_eq] at rw1
  rw[D_eq] at rw2
  exact rw1.2 (rw2.2 (A4 P Q R))

-- 前面证明了rw规则是蕴含在罗素公理内的，后续为了方便将使用rw这一策略
-- 更多的rw方法
theorem Or_assoc' (P Q R : Prop) : (((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R))) := by
  rw[@Rw_or_comm (P ∨ Q) R]
  rw[@Rw_or_comm P Q]
  rw[@Rw_or_comm Q R]
  rw[@Rw_or_comm P (R ∨ Q)]
  exact Or_assoc R Q P

theorem Rw_or_assoc (P Q R : Prop) : ((P ∨ (Q ∨ R)) = ((P ∨ Q) ∨ R)) := by
  rw[D_eq]
  constructor
  · exact Or_assoc P Q R
  · exact Or_assoc' P Q R

theorem Rw_not2 (P : Prop) : (¬¬P) = P := by
  rw[D_eq]
  constructor
  · exact Not2_l P
  · exact Not2_r P

theorem Rw_or2 (P : Prop) : (P ∨ P) = P := by
  rw[D_eq]
  constructor
  · exact A1 P
  · exact A2 P P

/- Todo：证明intro策略是可以在罗素公理中实现的（罗素公理完备性的一部分）
-- 完备性就是证明：如果可以在前提 h1, h2, ..., hn 的情况下证明 Γ, 那么就可以证明 h1 → h2 → ... → hn → Γ
-- 由分离定律，后者是显然可以推出前者的
-- intro策略就是前者推出后者，前提引入

-- 为了intro需要将一系列推理规则变为共同前提下的推理规则
-- 一共是三条：直接应用公理，带入规则（与应用公理是一样的），分离定律（最难证）
-/

-- 这个就是前两条规则, P是本就成立的公理/代入结果
theorem Intro1 (P Q : Prop) : Q → (P → Q) := by
  exact Imp_imp P Q

-- 推理过程：归结法
theorem Resol_g (P Q R : Prop) (h1 : P ∨ Q) (h2 : ¬P ∨ R) : (Q ∨ R) := by
  rw[← D1] at h2
  rw[← Rw_not2 Q] at h1
  rw[Rw_or_comm P ¬¬Q] at h1
  rw[← D1] at h1
  rw[← Rw_not2 Q]
  rw[← D1]
  exact Chain (¬Q) P R h2 h1

-- 为了方便后续使用，这里将其改为定理
-- 注意顺序
theorem Resol_g' (P Q R : Prop) : (¬P ∨ R) → (P ∨ Q) → (Q ∨ R) := by
  rw[← D1]
  rw[← Rw_not2 Q]
  rw[Rw_or_comm P ¬¬Q]
  rw[← D1]
  rw[← D1]
  exact Chain (¬Q) P R

-- 这个是有共同前提下的分离定律
-- 原本：(h1 : P → Q) (h2 : P) : Q
-- 注意！这是一个推理过程，不是一个定理
theorem Intro2 (P Q R : Prop) (h1 : P → Q → R) (h2 : P → Q) : (P → R) := by
  rw[D1] at h1
  rw[D1] at h2
  rw[D1]
  rw[D1] at h1
  rw[Rw_or_comm] at h1
  rw[← Rw_or_assoc] at h1
  rw[Rw_or_comm] at h2
  -- 注意：因为这里顺序是先h2后h1，所以后面改写需要先h2后h1
  let s1 := Resol_g Q (¬P) (R ∨ ¬P) h2 h1
  rw[Rw_or_comm]
  rw[← Rw_or2 ¬P]
  rw[Rw_or_assoc]
  rw[Rw_or_comm]
  exact s1

-- 写成罗素公理中的定理如下
-- 使用intro证明之后翻译
-- 好消息：rw是不需要改变的，所以没有那么多层展开
-- 实际上需要展开的是归结法
theorem Chain' (P Q R : Prop) : (P → (Q → R)) → (P → Q) → (P → R) := by
  /- 使用intro的做法
  intro h1 h2 h3
  exact h1 h3 (h2 h3)
  -/
  -- 这里不采用和Intro2一样的证明，因为这样的rw顺序才能使每次rw的位置是精确的
  rw[D1 P R]
  let s1 := Resol_g' Q (¬P) (R ∨ ¬P)
  rw[Rw_or_comm (¬P) R]
  rw[← Rw_or2 ¬P]
  rw[D1 P Q]
  rw[D1 P (Q → R)]
  rw[D1 Q R]
  rw[Rw_or_comm (¬P) (¬Q ∨ R)]
  rw[← Rw_or_assoc]
  rw[Rw_or_comm (¬P) Q]
  rw[Rw_or_assoc R (¬P) (¬P)]
  rw[Rw_or_comm (R ∨ ¬P) (¬P)]
  exact s1

-- 完备性：intro演示，如下
-- 这是前面的A4_l
-- 这是使用intro的证明
example (P Q R : Prop) : (Q → R) → ((Q ∨ P) → (R ∨ P)) := by
  intro h1
  let s1 := A3 Q P
  let s2 := A4 P Q R h1
  let s3 := A3 P R
  -- 本来不需要拆分的，但为了后面翻译方便，就拆了
  let s12_1 := Chain (Q ∨ P) (P ∨ Q) (P ∨ R)
  let s12_2 := s12_1 s2
  let s12 := s12_2 s1
  let s123_1 := Chain (Q ∨ P) (P ∨ R) (R ∨ P)
  let s123_2 := s123_1 s3
  let s123 := s123_2 s12
  exact s123

-- 以下是intro的逆向工程，对前者逐步翻译的
example (P Q R : Prop) : (Q → R) → ((Q ∨ P) → (R ∨ P)) := by
  -- 下面后缀带_h1就是加上了前提，什么都不带就是原证明中的结果，加了'就是对应的定理
  let h1 := (Q → R)
  -- Intro1，对于原本的直接引入公理，加上前提
  let s1' := (A3 Q P)
  let s1 := (Q ∨ P → P ∨ Q)
  let s1_h1 := Intro1 h1 s1 s1'
  -- 对于原本使用引入前提的分离定律，直接去掉引入前提即可
  -- s2这种：去掉h1，自然就是h1为前提的了
  let s2 := (P ∨ Q → P ∨ R)
  let s2_h1 := A4 P Q R
  -- s3
  let s3 := (P ∨ R → R ∨ P)
  let s3_h1 := Intro1 h1 s3 (A3 P R)
  -- 下面是原本s12中跳过的引入公理步骤
  let s12_1' := Chain (Q ∨ P) (P ∨ Q) (P ∨ R)
  let s12_1 := (P ∨ Q → P ∨ R) → ((Q ∨ P → P ∨ Q) → (Q ∨ P → P ∨ R))
  let s12_1_h1 := Intro1 h1 s12_1 s12_1'
  -- 下面进行第一次分离：s2
  let s12_2 := (Q ∨ P → P ∨ Q) → (Q ∨ P → P ∨ R)
  let s12_2_h1 := Intro2 h1 (P ∨ Q → P ∨ R) ((Q ∨ P → P ∨ Q) → (Q ∨ P → P ∨ R))
   s12_1_h1 s2_h1
  -- 第二次分离
  let s12 := (Q ∨ P → P ∨ R)
  let s12_h1 := Intro2 h1 (Q ∨ P → P ∨ Q) (Q ∨ P → P ∨ R)
   s12_2_h1 s1_h1
  -- 之后都是同理
  -- 引入定理s123_1'
  let s123_1' := Chain (Q ∨ P) (P ∨ R) (R ∨ P)
  let s123_1 := (P ∨ R → R ∨ P) → ((Q ∨ P → P ∨ R) → (Q ∨ P → R ∨ P))
  let s123_1_h1 := Intro1 h1 s123_1 s123_1'
  -- 分离s123_1和s3
  let s123_2 := (Q ∨ P → P ∨ R) → (Q ∨ P → R ∨ P)
  let s123_2_h1 := Intro2 h1 (P ∨ R → R ∨ P) ((Q ∨ P → P ∨ R) → (Q ∨ P → R ∨ P))
   s123_1_h1 s3_h1
  -- 分离s123_2和s12
  let s123 := (Q ∨ P → R ∨ P)
  let s123_h1 := Intro2 h1 (Q ∨ P → P ∨ R) (Q ∨ P → R ∨ P)
   s123_2_h1 s12_h1
  exact s123_h1

-- 使用多层intro的证明需要在证明Intro2之后才能实现
-- 因为，从第二层开始，我需要确切知道Intro2代表的证明过程才能在前面加入共同前提
-- 证明Chain'会大幅降低翻译工作量，因为不需要再展开Intro2中暗含的证明过程
-- 这一条是intro的演示，同时也可以证明结合律的正确性
theorem Intro_comm(P Q R : Prop) : (P → (Q → R)) → (Q → (P → R)) := by
  /- 使用intro的做法：
  intro h1 h2 h3
  exact h1 h3 h2
  -/
  sorry

end RusselComplete
