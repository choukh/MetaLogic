---
url: foundation.essential
---

# 元语言 ▸ 快速导入

## 前言

我们的研究对象是一阶逻辑等形式语言, 我们将其称为对象语言. 同时, 为了表达有关对象语言的命题和证明, 我们需要一个不同于对象语言的外部语言, 这个外部语言称为元语言. 传统上, 一阶逻辑等的元语言通常采用原始递归算术 (PRA) 等“低级”算术语言. 这主要是出于建立自下而上的逻辑体系以及满足有限主义哲学需求的考虑. 然而, 我们这里并不考虑这些因素, 而是采用一种称为[同伦类型论 (HoTT)](https://www.bananaspace.org/wiki/%E5%90%8C%E4%BC%A6%E7%B1%BB%E5%9E%8B%E8%AE%BA) 的“高级”语言作为元语言. 由于 HoTT 是一种更贴近数学实践的形式语言, 我们认为它可以在一定程度上兼顾形式上的严格与表达上的自然, 从而使完全形式化的讲义成为可能, 这也是我们的目标.

需要注意的是, HoTT 实际上是一系列理论的统称, 就像“集合论”有 ZFC, NBG, MK 等等一样. 本文具体使用的 HoTT 叫做 [Cubical Agda](https://agda.readthedocs.io/en/v2.6.4/language/cubical.html). 它非常严格, 以至于可以通过计算机来检查证明语句的正确性. 实际上它就是一种编程语言, 只不过其生态着重于数学证明而非软件应用. 借助 [Agda 的文学编程](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) 功能, [本 Markdown 文件](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) 实际上就是 Agda 源码, 可以直接做类型检查, 以检验证明语句的正确性. 基于这一特性, 我们实验性地采用以下排版方式: 非形式的自然语言与代码级的形式语言并行使用, 交替排列, 构成双重元语言, 以构筑对象语言. 我们会将 Agda 语句放在代码块中, 而自然语言则可以认为是对这些代码的注释, 具体样式请参看下一小节的凡例.

我们希望两种元语言可以相互解释, 互为补充. 当然, 这要求读者对 HoTT 和 Agda 都有一定的了解. 我们不会在本文中对这些内容进行详细的介绍, 而是假设读者已经具备了一定的基础. 如果读者对 HoTT 和 Agda 还不熟悉, 推荐阅读以下资料:

- HoTT入门: [HoTT Book](https://homotopytypetheory.org/book/)
- Agda + 泛等基础入门: [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
- 中文版快速参考: [Agda 泛等基础](https://www.yuque.com/ocau/hset/ti2u9nvok36hmibm)

接下来我们会快速复习一遍元语言中可以谈论的基础概念 (`Foundation.Essential`), 后篇中将直接使用 (`import`) 它们而不再额外定义.

```agda
module Foundation.Essential where
```

为了节省篇幅, 本篇也只是 `import` 更底层的已经定义好的模块, 请需要了解细节的读者自己查看[源码](https://github.com/choukh/MetaLogic/tree/main/src/Foundation). 简单来说, 这些模块只不过是对 [Cubical 标准库](https://github.com/agda/cubical) 的重新封装, 以满足我们的特殊需求: 尽可能使用**命题相等 (Propositional Equality)** 而不是**道路 (Path)**, 以方便我们的形式化, 因为我们不涉及高阶同伦概念.

## 凡例

### 定义

定义的自然语言表述 叫做 定义名 (`definition_name`).

**<u>定义</u>** 定义名 (`definition_name = definition_term`).

**<u>定义</u>** 定义名 (`definition_name`), 当且仅当 定义的自然语言表述.

### 不带证明的定理

定理的自然语言表述 (`theorem_name`).

**<u>定理</u>** 定理名 (`theorem_name : Theorem_Type`).

**<u>定理</u> `theorem_name`** 定理的自然语言表述.

### 带证明的定理

**<u>定理</u>** 定理名: 定理的自然语言表述.  
**<u>证明</u>** 定理的自然语言证明. ∎

```PlainText
theorem_name : Theorem_Type
theorem_name = proof_term
```

## 前奏

前奏 (`Prelude`) 是基础中的基础, 是定义其他基础概念所必须的基础概念, 以至于有些是原始概念, 如道路类型. 这些原始概念具体涉及到 Cubical 类型论的规则, 这里不深入其细节, 而只作为一个黑盒使用.

### 内置

```agda
open import Foundation.Prelude.Builtin public
```

内置 (`Builtin`) 模块主要包括带魔法 (编译器支持) 的一些原始概念, 如宇宙和道路类型等, 以及一些基本数据类型:

- 宇宙: 类型宇宙 `𝕋`, 宇宙层级 `Level`, 零级宇宙 `0ℓ`, 后继宇宙 `_⁺`, 宇宙二元并 `_⊔_`, 所有有限层级宇宙所居留的宇宙 `𝕋ω`
- 同一性类型: 命题相等类型 `_≡_`, 道路类型 `_≡🧊_`
- 基本数据类型: 单元类型 `⊤`, 布尔类型 `𝔹`, 自然数类型 `ℕ`, 列表 (不定长可数有限) 类型 `𝕃`, Σ类型 `Σ`

注意, 对某些相似概念的 Cubical 版本, 我们会在其名字中带上“🧊”, 以示区别. 此外, 我们对符号作如下约定:

- 宇宙层级序号 `ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level`
- 任意给定宇宙的类型 `A B C D X : 𝕋 ℓ`
- 类型族 / 性质 / 一元关系 `P Q : A → 𝕋 ℓ`
  ※ 我们保留“谓词”这个名称给可以证明是命题的一元关系
- 二元关系 `R R₁ R₂ : A → B → 𝕋 ℓ`
- 依值类型族 `P₂ Q₂ : (x : A) → P x → 𝕋 ℓ`

我们约定Σ类型 `Σ A (λ x → P)`, 即满足 `P` 的 `A`, 可以简记为 `Σ x ꞉ A ， P` 或者 `Σ x ， P`.

### 函数

```agda
open import Foundation.Prelude.Function public
```

**<u>定义</u>** 与函数有关的一些便利记法

- 恒等函数 `id = λ x → x`
- 恒等函数性 `isId = λ f → ∀ x y → f x ≡ f y`
- 函数复合 `f ∘ g = λ x → f (g x)`
  - 二元 `f ∘₂ g = λ x y → f (g x y)`
  - 三元 `f ∘₃ g = λ x y z → f (g x y z)`
- 参数翻转 `flip = λ f x y → f y x`
- 函数应用 `f $ x = f x`, 用于当参数本身是个函数应用时省略参数外层的括号

### 命题相等

```agda
open import Foundation.Prelude.Equality public
```

**<u>定理</u>** 相等的基本性质

- 对称性 `sym`, 传递性 `_∙_`
  - 注意自反性 `refl` 不需要专门给出, 它是相等类型的唯一构造子
- 合同性 `cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y`
  - 二元 `cong2 : ∀ (f : A → B → C) {x y z w} → x ≡ y → z ≡ w → f x z ≡ f y w`
- 等量替换 `subst : (P : A → 𝕋 ℓ) {x y : A} → y ≡ x → P x → P y`
  - 二元 `subst2 : (R : A → B → 𝕋 ℓ) {x y : A} {z w : B} → x ≡ y → z ≡ w → R x z → R y w`
- 函数外延性 `funExt : {P : A → 𝕋 ℓ} {f g : (x : A) → P x} → ((x : A) → f x ≡ g x) → f ≡ g`
  - 二元 `funExt2 : {R : A → B → 𝕋 ℓ} {f g : (x : A) (y : B) → R x y} → ((x : A) (y : B) → f x y ≡ g x y) → f ≡ g`
- 函数外延性的逆 `funExt⁻ : {P : A → 𝕋 ℓ} {f g : (x : A) → P x} → f ≡ g → (x : A) → f x ≡ g x`
- 同构蕴含相等 `ua : A ≅ B → A ≡ B`

其中同构定义为一对互逆的函数; "ua" 是泛等公理 (univalence axiom) 的缩写, 虽然在 Cubical 中它是定理, 出于历史原因仍记作 "ua".

### 同伦层级

```agda
open import Foundation.Prelude.HLevel public
```

如果说宇宙层级是类型宇宙 `𝕋 ℓ` 所具有的一种属性, 那么同伦层级 (hLevel) 则是类型 `A : 𝕋 ℓ` 所具有的一种属性. 我们只关心同伦层级为 1 和 2 的两种类型.

同伦层级为 1 的类型叫做命题, 该类类型的任意两个项都可证相等. "类型 `A` 是命题" 表达为 `isProp A`. 如所期待的那样, 类型 `isProp A` 也是一个命题, 即对任意 `A : 𝕋 ℓ` 可证 `isProp (isProp A)`. 我们也说 `isProp` 是一个谓词.

同伦层级为 2 的类型叫做集合, 该类类型的任意两个项的相等都是命题, 即给定两个项相等的任意两个证明, 这两个证明是相等的. "类型 `A` 是集合" 表达为 `isSet A`. 与 `isProp` 一样, `isSet` 也是一个谓词. 此外我们有 `isProp→isSet`, 即任意命题都是集合. 直观上, 由于命题的任意项都相等, 那么这些项之间的相等的方式也应该是相等的, 所以命题也是集合.

对于嵌套的Π类型, 不管嵌套多少次, 只要最后的目标是命题 (或集合), 那么整个嵌套Π类型也是命题 (或集合). 如果构成Σ类型的两边都是命题 (或集合), 那么这个Σ类型也是命题 (或集合).

**<u>约定</u>** 集族 (涉及集合的Π类型)

对于一个类型族, 如果能证明其中的每个类型都是集合, 我们会说它是一个集族. 即使没有提供证明, 我们也可能会这样说, 读者应该理解为我们是在暗示这样的证明存在, 只是后续理论的构筑中不需要它.

**<u>约定</u>** n元组 (涉及集合的Σ类型)

我们只会把集合算作n元组的分量. 例如当我们说某 `A` 的 `B` 是一个2元组

1. 值域为 `A` 的一个函数 `f`
2. `A` 的一个满足 `P` 的 `C`

时, 读者应该理解为我们通常只会谈论某集合 `A` 的 `B`, 且 `P` 是一个命题, `C` 是一个集合. 同样地, 这些证明不一定会给出, 我们只是暗示可证.


### 其他

```agda
open import Foundation.Prelude.Misc public
```

为了编码上的方便, 我们经常需要用 Agda 的反射机制定义的宏 `declareRecordIsoΣ` 将Σ类型与 record 类型相互转化. 我们把具有某种结构的类型宇宙叫做 `TypeWithStr`. 它其实就是一个Σ类型, 其左投影 `typ` 用于取得底类型, 右投影 `str` 用于取得底类型所带的结构.

## 命题

元语言中需要能构造数学对象, 并且能谈论这些对象的性质. 前者由同伦层级为 2 的类型 (集合) 承担, 后者则由同伦层级为 1 的类型 (命题) 承担. 它们都是类型, 有统一的一些规则. 例如, 同样一个**类型形成子 (type former)** `→`, 作用于集合就成了函数, 作用于命题就成了蕴含. 本节将介绍关于命题的基本概念.

### 命题截断

```agda
open import Foundation.Prop.Truncation public
```

命题截断 `∥_∥₁` 用于把一个可能不是命题的类型转化为命题. 命题截断是一个高阶归纳类型, 其构造子 `∣_∣₁` 用于构造命题截断的项, `𝟙.squash` 用于证明命题截断后的类型的项确实都是相等的.

**<u>定理</u>** 命题截断的性质

- `𝟙.rec` : 如果目标 `P` 是命题, 那么我们可以通过证明 `A → P` 来证明 `∥ A ∥₁ → P`
- `𝟙.rec2` : 如果目标 `P` 是命题, 那么我们可以通过证明 `A → B → P` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → P`
- `𝟙.elim` : `𝟙.rec` 的依值版本
- `𝟙.elim2` : `𝟙.rec2` 的依值版本
- `𝟙.map` : 可以通过证明 `A → B` 来证明 `∥ A ∥₁ → ∥ B ∥₁`
- `𝟙.map2` : 可以通过证明 `A → B → C` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁`
- `𝟙.rec→Set` : 如果目标 `B` 是集合, 且 `f : A → B` 是常函数, 那么我们可以通过 `f` 来构造 `∥ A ∥₁ → B`

### 逻辑

```agda
open import Foundation.Prop.Logic public
```

#### 无需截断

以下逻辑概念由相应的类型形成子直接承担, 而无需截断. 因为这些类型形成子作用于命题之上, 得到的类型也是命题.

- 蕴含 `→`, 只要右边是命题就是命题
- 否定 `¬_`, 对任意类型都是命题
- 合取 `_×_`, 要求两边都是命题
- 全称量化 `∀ x →`, 只要右边是命题就是命题

**<u>定理</u>** 命题截断上的归谬法 `exfalso₁ : ∥ A ∥₁ → ¬ A → B`.

#### 析取

逻辑析取 `_∨_` 定义为**和类型 (sum type)** 的命题截断, 即 `A ∨ B = ∥ A ⊎ B ∥₁`. 因为和类型的项起码有两种 (左边或右边) 不同的构造方式, 但析取不关心具体是哪种, 所以必须要做命题截断, 以确保所有证明项都相等. 我们有析取的引入规则 `inl` 和 `inr`, 对于消去我们直接使用模式匹配.

注意对比合取. 我们不需要对积类型做命题截断以得到合取, 因为当 `_×_` 的两边都是命题的时候, 它的项只有一种构造方式, 所以它们之间的相等是自然成立的.

#### 存在量化

存在量化 `∃` 定义为**Σ类型 (sigma type)** 的命题截断, 即 `∃ A P = ∥ Σ A P ∥₁`. 因为Σ类型的项可能存在多种构造方式, 但存在量化不关心具体是哪种, 只要存在就行. 我们有存在量化的引入规则 `ex`, 对于消去我们直接使用模式匹配. 我们约定 `∃ A (λ x → P)` 可以简记为 `∃ x ꞉ A ， P` 或者 `∃ x ， P`.

### 逻辑等价

```agda
open import Foundation.Prop.Iff public
```

逻辑等价 `_↔_`, 也叫当且仅当 (iff), 定义为双向蕴含, 它是一个等价关系 (`↔-refl`, `↔-sym`, `↔-trans`). 只有当左右两边都是命题的时候, 逻辑等价才有意义. 此时, 它也是一个命题 (`isProp↔`).

注意, 我们把逻辑等价定义为了一个 record 类型, 必要时可以用宏转化为Σ类型. 该 record 类型的构造子 `⇒:_⇐:_` 充当了逻辑等价的引入规则, 消去规则则由 record 类型的投影 `.⇒` 和 `.⇐` 给出.

### 命题宇宙

```agda
open import Foundation.Prop.Universe public
```

命题宇宙 `ℙ ℓ` 定义为带结构 `isProp` 的类型宇宙 `𝕋 ℓ`, 即 `ℙ ℓ = TypeWithStr ℓ isProp`. 继承自类型宇宙的层级, 命题宇宙也分层级, 其中最底层记作 `ℙ₀`.

我们用粗体的**命题**指代命题宇宙的项, 以区分作为类型的命题. 我们约定使用 `𝗣 𝗤 𝗥` 等符号表示**命题**. “**命题** `𝗣` 成立”记作 `𝗣 holds`, 定义为左投影 `typ 𝗣`. 而右投影 `str 𝗣` 则说明了 `𝗣 holds` 确实是一个命题.

**<u>定义</u>** **命题**的实例

- 恒假**命题** `⊥ₚ`, 定义为 `⊥ , isProp⊥`, 因为 `⊥` 是一个命题
- 恒真**命题** `⊤ₚ`, 定义为 `⊤ , isProp⊤`, 因为 `⊤` 是一个命题

**<u>定理</u>** **命题**的性质

- 任意层级的命题宇宙 `ℙ ℓ` 本身是一个集合, 该性质记作 `isSetℙ`
- 命题外延性 `propExt : isProp A → isProp B → A ↔ B → A ≡ B`
- **命题**外延性 `ℙExt : 𝗣 holds ↔ 𝗤 holds → 𝗣 ≡ 𝗤`
- 命题截断外延性 `propTruncExt : A ↔ B → ∥ A ∥₁ ≡ ∥ B ∥₁`
- **命题**截断外延性 `ℙTruncExt : A ↔ B → ∥ A ∥ₚ ≡ ∥ B ∥ₚ`

其中**命题**截断 `∥ A ∥ₚ` 定义为 `∥ A ∥₁ , 𝟙.squash`.

## 集合

元语言中的集合主要包括一些数据类型, 例如自然数, 列表等, 在后面的小节单独介绍. 除此之外, 我们谈论的集合主要是幂集.

### 幂集

```agda
open import Foundation.Set.Powerset public
```

给定任意类型 `X : 𝕋 ℓ`, 我们把 `X` 到命题宇宙 `ℙ ℓ` 的函数叫做 `X` 的幂集, 记作 `𝒫 X`, 它的项也叫 `X` 的子集. 可以证明幂集确实是一个集合 (`isSet𝒫`).

给定项 `x : X` 和子集 `A : 𝒫 X`, 属于关系 `x ∈ A` 定义为 `A x holds`. `A` 是取值到 `ℙ ℓ` 的函数, 这保证了属于关系是取值到命题的 (`isProp∈`).

### 集合截断

```agda
open import Foundation.Set.Truncation public
```

与命题截断类似地, 我们有集合截断 `∥_∥₂`, 它将高阶群胚截断为集合.

**<u>定理</u>** 集合截断的性质

- `𝟚.rec` : 如果目标 `B` 是命题, 那么我们可以通过证明 `A → B` 来证明 `∥ A ∥₂ → B`
- `𝟚.rec2` : 如果目标 `C` 是命题, 那么我们可以通过证明 `A → B → C` 来证明 `∥ A ∥₂ → ∥ B ∥₂ → C`
- `𝟚.elim` : `rec2→s` 的依值版本
- `𝟚.elim2` : `rec2²→s` 的依值版本
- `𝟚.map` : 可以通过证明 `A → B` 来证明 `∥ A ∥₂ → ∥ B ∥₂`
- `𝟚.map2` : 可以通过证明 `A → B → C` 来证明 `∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂`

### 集合宇宙

```agda
open import Foundation.Set.Universe public
```

与命题宇宙类似地, 集合宇宙 `𝕊 ℓ` 定义为 `𝕋 ℓ` 配备上结构 `isSet`, 即 `𝕊 ℓ = TypeWithStr ℓ isSet`. 但我们中一般不直接使用 `𝕊`. 为了方便处理, 我们会尽可能地使用它们的柯里化版本, 即说 "给定类型 `A`, 如果它是命题 (或集合), 那么怎么怎么样", 而不说 "给定**命题** (或**集合**) `𝗔`, 怎么怎么样". 需要注意的是, 集合宇宙 `𝕊 ℓ` 本身不是集合, 而是一个群胚.

## 数据类型

数据类型又叫归纳类型, 可以简单地认为它们就是一些良基树, 树的节点叫做构造子. 例如自然数类型 `ℕ` 的构造子有 `zero` 和 `suc`, 我们可以构造自然数的项, 例如 `suc (suc zero)`. 我们把数据类型分成四类: 命题, 集合, 组合, 容器.

### 命题

命题数据类型只有两种: 空类型 `⊥` 与单元类型 `⊤`, 它们分别具有基数 $0$ 和 $1$.

#### 空类型

```agda
open import Foundation.Data.Empty public
```

空类型 `⊥` 没有任何构造子, 所以它没有任何项, 也就是说它是不可证的命题, 即恒假. 空类型 `⊥` 是命题 (`isProp⊥`), 也是集合 (`isSet⊥`). 空类型 `⊥` 位于 `𝕋₀`, 但我们还有一个宇宙多态版的空类型 `⊥* : 𝕋 ℓ`, 它也是命题 (`isProp⊥*`), 也是集合 (`isSet⊥*`).

#### 单元类型

```agda
open import Foundation.Data.Unit public
```

单元类型 `⊤` 只有一个构造子 `tt`, 所以它只有一个项, 也就是说它是恒真的命题. 单元类型 `⊤` 是命题 (`isProp⊤`), 也是集合 (`isSet⊤`). 单元类型 `⊤` 位于 `𝕋₀`, 但我们还有一个宇宙多态版的单元类型 `⊤* : 𝕋 ℓ`, 它也是命题 (`isProp⊤*`), 也是集合 (`isSet⊤*`).

### 集合

集合数据类型有可数多个, 我们主要关心的是布尔类型 `𝔹` 和自然数类型 `ℕ`, 它们分别具有基数 $2$ 和 $\aleph_0$. 注意这里使用了 $\LaTeX$, 仅限于本篇, 它们是元元语言.

#### 布尔类型

```agda
open import Foundation.Data.Bool public
```

布尔类型 `𝔹` 有两个构造子 `true` 和 `false`. 布尔类型 `𝔹` 是集合 (`isSet𝔹`).

#### 自然数类型

```agda
open import Foundation.Data.Nat public
```

自然数类型 `ℕ` 有两个构造子 `zero` 和 `suc : ℕ → ℕ`. 自然数类型 `ℕ` 是集合 (`isSetℕ`).

### 组合

组合数据类型用于对任意给定的两个类型做某种形式的组合.

#### Σ类型

```agda
open import Foundation.Data.Sigma public
```

Σ类型 `Σ A P` 的项具有 `(x , p)` 的形式, 其中 `x : A` 而 `p : P x`. Σ类型具有基数 $\sum_{x \in A} |P(x)|$. 如果 `A` 和 `P x` 都是命题 (或集合), 那么这个 `Σ A P` 也是命题 (或集合).

当 `P` 不依值于 `A` 的时候就成了普通的积类型 `A × B`, 它的项具有 `(a , b)` 的形式, 其中 `a : A` 而 `b : B`. 积类型具有基数 $|A| \times |B|$. 如果 `A` 和 `B` 都是命题 (或集合), 那么这个 `A × B` 也是命题 (或集合).

#### 和类型

```agda
open import Foundation.Data.Sum public
```

和类型 `A ⊎ B` 就是对类型 `A` 和 `B` 做不交并, 它的项具有 `inl a` 或 `inr b` 的形式, 其中 `a : A` 而 `b : B`. 和类型具有基数 $|A| + |B|$. 如果 `A` 和 `B` 都是命题且它们互斥, 那么这个 `A ⊎ B` 是命题; 如果 `A` 和 `B` 都是集合, 那么这个 `A ⊎ B` 是集合.

### 容器

容器数据类型以某种形式容纳了另一个给定类型 `A` 的某些项.

#### 列表

```agda
open import Foundation.Data.List public
```

列表 `𝕃 A` 是不定长可数有限类型. 不定长是指列表的类型签名中不储存长度信息, 可数是指列表的项有一个典范线序, 有限是指列表的长度是个自然数. 当 `A` 是集合时, `𝕃 A` 也是集合 (`isSet𝕃`).

我们可以问 `x : A` 在不在列表 `xs : 𝕃 A` 中, 这引入了列表的属于关系 `x ∈ᴸ xs` 以及一系列类比于集合论的概念. 我们把它们放在以下模块. 注意与幂集不同的是, `x ∈ᴸ xs` 不是命题, 因为 `x` 不保证在 `xs` 中只出现一次.

```agda
open import Foundation.Data.List.SetTheoretic public
  renaming (_∈_ to _∈ᴸ_; _∉_ to _∉ᴸ_)
```

**<u>定义</u>** 列表的无穷序列 (`f : 𝕃ₙ A`) 的一个累积 (`Cumulation f`) 是一个以 `n : ℕ` 为索引的集族, 对每个 `n` 都给出了一个 `xs : 𝕃 A`, 使得 `f n ≡ f m ++ xs` 成立. 其中 `_++_` 是列表的拼接操作.

```agda
open import Foundation.Data.List.Cumulation public
  using (𝕃ₙ; Cumulation)
```

#### 向量

```agda
open import Foundation.Data.Vec public
```

向量 `𝕍 A n` 是定长可数有限类型. 定长是指向量的类型签名中储存了长度信息 `n`. 当 `A` 是集合时, `𝕍 A n` 也是集合 (`isSet𝕍`).

我们可以问 `x : A` 在不在向量 `x⃗ : 𝕍 A n` 中, 这引入了向量的属于关系 `x ∈⃗ x⃗` 以及一系列类比于集合论的概念. 我们把它们放在以下模块. 注意与幂集不同的是, `x ∈⃗ x⃗` 不是命题, 因为 `x` 不保证在 `x⃗` 中只出现一次.

```agda
open import Foundation.Data.Vec.SetTheoretic public
  renaming (_∈_ to _∈⃗_; Any to Any⃗)
```

## 函数

函数 `A → B` 在我们的元语言里是原始概念. 以下列出一些关于函数的常用概念.

### 序列

```agda
open import Foundation.Function.Sequance public
```

我们把函数 `ℕ → A` 称为无穷序列 `InfSeq`, 它有 “希尔伯特旅馆”操作 `_∷ₙ_`, 第一个参数是安排到0号房间的新客人, 第二个参数是原来的客房安排.

### 同构

```agda
open import Foundation.Function.Isomorphism public
```

同构 (`_≅_`) 是类型间的一对互逆的函数, 它构成了类型宇宙中的一种等价关系 (`idIso`, `invIso`, `compIso`).

**<u>定理</u> `univalence`** 当 `A` 是集合的时候, `A ≡ B` 与 `A ≅ B` 同构.

### 双射

```agda
open import Foundation.Function.Bijection public
```

**<u>定义</u>**

- 单射性 `injective = λ f → ∀ {x y} → f x ≡ f y → x ≡ y`
- 满射性 `surjective = λ f → ∀ y → ∃ x ， f x ≡ y`
- 双射性 `bijective = λ f → injective f × surjective f`

它们都是命题 (`isPropInjective`, `isPropSurjective`, `isPropBijective`).

**<u>定义</u>**

- 单射 `A ↣ B = Σ (A → B) injective`
- 满射 `A ↠ B = Σ (A → B) surjective`
- 双射 `A ⤖ B = Σ (A → B) bijective`

**<u>定理</u> `Iso≡Bij`** 如果 `A` 和 `B` 都是集合, 那么 `A ≅ B` 与 `A ⤖ B` 相等.

## 关系

关系是取值到 `𝕋 ℓ` 的n元函数. 以下按元数列出几种常用关系.

### 零元关系

零元关系就是命题. 我们主要关心 `⊥` 这个命题, 并把它的衍生概念都放在零元关系 `Nullary` 模块中.

#### 否定

```agda
open import Foundation.Relation.Nullary.Negation public
```

**<u>定义</u>** 否定的相关概念

- 否定 `¬_ = λ A → A → ⊥`
- 非空 `nonEmpty = λ A → ¬ ¬ A`
- 稳定 `Stable = λ A → nonEmpty A → A`

#### 可判定

```agda
open import Foundation.Relation.Nullary.Decidable public
```

**<u>定义</u>** `A` 可判定, 记作 `Dec A`, 当且仅当 `A` 或 `¬ A`.

如果 `A` 是一个命题, 那么其可判定性 `Dec A` 也是一个命题 (`isPropDec`).

#### 离散

```agda
open import Foundation.Relation.Nullary.Discrete public
```

**<u>定义</u>** `A` 离散, 当且仅当 `A` 上的 `_≡_` 可判定.

如果一个类型是离散的, 那么它是一个集合 (`discrete→isSet`). 如果一个类型是集合, 那么它的离散性是一个命题 (`isPropDiscrete`). 离散集合宇宙 `𝔻 ℓ` 定义为 `TypeWithStr ℓ discrete`, 也叫经典集合宇宙.

### 一元关系

#### 可数

```agda
open import Foundation.Relation.Unary.Countable public
```

**<u>定义</u>**

- `A` 可数 (`countable`), 当且仅当存在 `A` 到 `ℕ` 的单射 `A ↣ ℕ`
- `A` 可数无限 (`countablyInfinite`), 当且仅当存在 `A` 到 `ℕ` 的同构 `A ≅ ℕ`
- `A` 无限 (`infinite`), 当且仅当存在 `ℕ` 到 `A` 的单射 `ℕ ↣ A`

#### 可枚举

```agda
open import Foundation.Relation.Unary.Enumerable as E public
open E.ListView public
```

**<u>定义</u>** `A` 可枚举, 当且仅当存在函数 `f : ℕ → A ⊎ ⊤`, 使得对任意 `x : A`, 存在 `n` 满足 `f n ≡ x`.

**<u>定理</u> `discr→enum→count`** 如果 `A` 离散 (这意味着 `A` 是集合), 并且 `A` 可枚举, 那么 `A` 可数.

我们通常使用可枚举的另一种定义:

**<u>定义</u>** `A` 可枚举, 当且仅当存在 `A` 的一个枚举 `Enum A`, 它是一个二元组
1. 使得条件 `wit` 成立的列表无穷序列 `enum : 𝕃ₙ A`. 其中 `wit` 是说对任意 `x : A`, 存在 `n` 满足 `x ∈ᴸ enum n`
2. `f` 的一个累积 `cum : Cumulation f`

可枚举的这两种定义是逻辑等价的 (`enumerable↔Ⓜ`).

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Essential.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.essential)  
> 交流Q群: 893531731
