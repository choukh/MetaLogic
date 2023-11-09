---
url: foundation.essential
---

# 元语言

## 前言

我们的研究对象是一阶逻辑等形式语言, 我们将其称为对象语言. 同时, 为了表达有关对象语言的命题和证明, 我们需要一个不同于对象语言的外部语言, 这个外部语言称为元语言. 传统上, 一阶逻辑等的元语言通常采用原始递归算术 (PRA) 等“低级”算术语言. 这主要是出于建立自下而上的逻辑体系以及满足有限主义哲学需求的考虑. 然而, 我们这里并不考虑这些因素, 而是采用一种称为[同伦类型论 (HoTT)](https://www.bananaspace.org/wiki/%E5%90%8C%E4%BC%A6%E7%B1%BB%E5%9E%8B%E8%AE%BA) 的“高级”语言作为元语言. 由于 HoTT 是一种更贴近数学实践的形式语言, 我们认为它可以在一定程度上兼顾形式上的严格与表达上的自然, 从而使完全形式化的讲义成为可能, 这也是我们的目标.

需要注意的是, HoTT 实际上是一系列理论的统称, 就像“集合论”有 ZFC, NBG, MK 等等一样. 本文具体使用的 HoTT 叫做 [Cubical Agda](https://agda.readthedocs.io/en/v2.6.4/language/cubical.html). 它非常严格, 以至于可以通过计算机来检查证明语句的正确性. 实际上它就是一种编程语言, 只不过其生态着重于数学证明而非软件应用. 借助 [Agda 的文学编程](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) 功能, [本 Markdown 文件](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) 实际上就是 Agda 源码, 可以直接做类型检查, 以检验证明语句的正确性. 基于这一特性, 我们实验性地采用以下编排方式: 非形式的自然语言与代码级的形式语言并行使用, 交替排列, 构成双重元语言, 以构筑对象语言. 我们会将 Agda 语句放在代码块中, 而正文的自然语言则可以认为是对这些代码的注释. 我们希望两种元语言可以相互解释, 互为补充.

当然, 这要求读者对 HoTT 和 Agda 都有一定的了解. 我们不会在本文中对这些内容进行详细的介绍, 而是假设读者已经具备了一定的基础. 如果读者对 HoTT 和 Agda 还不熟悉, 我们推荐读者阅读以下资料:

- HoTT入门: [HoTT Book](https://homotopytypetheory.org/book/)
- Agda + 泛等基础入门: [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
- 中文版快速参考: [Agda 泛等基础](https://www.yuque.com/ocau/hset/ti2u9nvok36hmibm)

以下快速复习一遍元语言中可以谈论的基础概念, 后篇中将直接使用 (`import`) 它们而不再额外定义. 为了节省篇幅, 本篇也只是 `import` 更底层的已经定义好的模块, 请需要了解细节的读者自己查看[源码](https://github.com/choukh/MetaLogic/tree/main/src/Foundation). 简单来说, 这些模块只不过是对 [Cubical 标准库](https://github.com/agda/cubical) 的重新封装, 以满足我们的特殊需求: 尽可能使用命题相等 (Propositional Equality) 而不是道路 (Path), 以方便我们的形式化, 因为我们不涉及高阶同伦概念.

```agda
module Foundation.Essential where
```

## 前奏

前奏 (Prelude) 是基础中的基础, 是定义其他基础概念所必须的基础概念, 以至于有些是原始概念, 如道路类型. 这些原始概念具体涉及到 Cubical 类型论的规则, 这里不深入其细节, 而只作为一个黑盒使用.

### 内置

```agda
open import Foundation.Prelude.Builtin public
```

内置 (Builtin) 模块主要包括带魔法 (编译器支持) 的一些原始概念, 如宇宙和道路类型等, 以及一些基本数据类型:

- 宇宙: 类型宇宙 `𝕋`, 宇宙层级 `Level`, 零级宇宙 `0ℓ`, 后继宇宙 `_⁺`, 宇宙二元并 `_⊔_`, 宇宙提升 `Lift`
- 同一性类型: 命题相等类型 `_≡_`, 道路类型 `_≡🧊_`
- 基本数据类型: 单元类型 `⊤`, 布尔类型 `𝔹`, 自然数类型 `ℕ`, 列表 (有序不定长有限集合) 类型 `𝕃`, Σ类型 `Σ`

注意, 对某些相似概念的 Cubical 版本, 我们会在其名字中带上“🧊”, 以示区别. 此外, 我们对符号作如下约定:

- 宇宙层级序号 `ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level`
- 任意给定宇宙的类型 `A B C D T : 𝕋 ℓ`
- 类型族 / 性质 / 一元关系 `P Q : A → 𝕋 ℓ`
- 二元关系 `R S : A → B → 𝕋 ℓ`
- 依值类型族 `P₂ Q₂ : (x : A) → P x → 𝕋 ℓ`

注意当我们说“任意给定”的时候指的是 arbitrary, 而对于 forall, 我们一定会说“所有”或“对任意”. 我们保留“谓词”这个名称给可以证明是命题的一元关系. 最后, 我们约定Σ类型 `Σ A (λ x → P)`, 即满足 `P` 的 `A`, 可以简记为 `Σ x ꞉ A ， P` 或者 `Σ x ， P`.

### 函数

```agda
open import Foundation.Prelude.Function public
```

前奏中的函数模块主要定义与函数有关的一些便利记法:

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

本模块给出了相等的基本性质:

- 对称性 `sym`, 传递性 `_∙_`
  - 注意自反性 `refl` 不需要专门给出, 它是相等类型的唯一构造子
- 合同性 `cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y`
  - 二元 `cong2 : ∀ (f : A → B → C) {x y z w} → x ≡ y → z ≡ w → f x z ≡ f y w`
- 等量替换 `subst : (P : A → 𝕋 ℓ) {x y : A} → y ≡ x → P x → P y`
  - 二元 `subst2 : (R : A → B → 𝕋 ℓ) {x y : A} {z w : B} → x ≡ y → z ≡ w → R x z → R y w`
- 函数外延性 `funExt : {P : A → 𝕋 ℓ} {f g : (x : A) → P x} → ((x : A) → f x ≡ g x) → f ≡ g`
  - 二元 `funExt2 : {R : A → B → 𝕋 ℓ} {f g : (x : A) (y : B) → R x y} → ((x : A) (y : B) → f x y ≡ g x y) → f ≡ g`
- 函数外延性的逆 `funExt⁻ : {P : A → 𝕋 ℓ} {f g : (x : A) → P x} → f ≡ g → (x : A) → f x ≡ g x`

以及与同伦等价 `_≃_` 和同构 `_≅_` 相关的性质:

- 同伦等价蕴含相等 `ua≃ : A ≃ B → A ≡ B`
- 同构蕴含相等 `ua : A ≅ B → A ≡ B`

注意 ua 是泛等公理 (univalence axiom) 的缩写, 虽然在 Cubical 中它是定理, 出于历史原因仍记作 ua.

### 同伦层级

```agda
open import Foundation.Prelude.HLevel public
```

如果说宇宙层级是类型宇宙 `𝕋 ℓ` 所具有的一种属性, 那么同伦层级 (hLevel) 则是类型 `A : 𝕋 ℓ` 所具有的一种属性. 我们只关心同伦层级为 1 和 2 的两种类型.

同伦层级为 1 的类型叫做命题, 该类类型的任意两个项都可证相等. "类型 `A` 是命题" 表达为 `isProp A`. 如所期待的那样, 类型 `isProp A` 也是一个命题, 即对任意 `A : 𝕋 ℓ` 可证 `isProp (isProp A)`. 我们也说 `isProp` 是一个谓词.

同伦层级为 2 的类型叫做集合, 该类类型的任意两个项的相等都是命题, 即给定两个项相等的任意两个证明, 这两个证明是相等的. "类型 `A` 是集合" 表达为 `isSet A`. 与 `isProp` 一样, `isSet` 也是一个谓词. 此外我们有 `isProp→isSet`, 即任意命题都是集合. 直观上, 由于命题的任意项都相等, 那么这些项之间的相等的方式也应该是相等的, 所以命题也是集合.

对于嵌套的Π类型, 不管嵌套多少次, 只要最后的目标是命题 (或集合), 那么整个嵌套Π类型也是命题 (或集合). 如果构成Σ类型的两边都是命题 (或集合), 那么这个Σ类型也是命题 (或集合).

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

命题截断 `∥_∥₁` 用于把一个可能不是命题的类型转化为命题. 命题截断是一个高阶归纳类型, 其构造子 `∣_∣₁` 用于构造命题截断的项, `is1` 用于证明命题截断后的类型的项确实都是相等的. 有以下常用引理:

- `rec1` : 如果目标 `P` 是命题, 那么我们可以通过证明 `A → P` 来证明 `∥ A ∥₁ → P`
- `rec1²` : 如果目标 `P` 是命题, 那么我们可以通过证明 `A → B → P` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → P`
- `map1` : 可以通过证明 `A → B` 来证明 `∥ A ∥₁ → ∥ B ∥₁`
- `map1²` : 可以通过证明 `A → B → C` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁`
- `elim1` : `rec1` 的依值版本
- `elim1²` : `rec1²` 的依值版本

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

以下是**命题**的一些实例和性质:

- 恒假**命题** `⊥ₚ`, 定义为 `⊥ , isProp⊥`, 因为 `⊥` 是一个命题
- 恒真**命题** `⊤ₚ`, 定义为 `⊤ , isProp⊤`, 因为 `⊤` 是一个命题
- 任意层级的命题宇宙 `ℙ ℓ` 本身是一个集合, 该性质记作 `isSetℙ`
- 命题外延性 `propExt : isProp A → isProp B → A ↔ B → A ≡ B`
- **命题**外延性 `ℙExt : 𝗣 holds ↔ 𝗤 holds → 𝗣 ≡ 𝗤`
- 命题截断外延性 `propTruncExt : A ↔ B → ∥ A ∥₁ ≡ ∥ B ∥₁`
- **命题**截断外延性 `ℙTruncExt : A ↔ B → ∥ A ∥ₚ ≡ ∥ B ∥ₚ`

其中**命题**截断 `∥ A ∥ₚ` 定义为 `∥ A ∥₁ , is1`.

## 集合

```agda
open import Foundation.Set.Powerset public
```

## 函数

```agda
open import Foundation.Function.Bundles public
open import Foundation.Function.Sequance public
```

## 数据类型

```agda
open import Foundation.Data.Empty public
open import Foundation.Data.Unit public
open import Foundation.Data.Bool public
open import Foundation.Data.Nat public
open import Foundation.Data.Sigma public
open import Foundation.Data.Sum public
open import Foundation.Data.List public
open import Foundation.Data.Vec public
```

## 关系

```agda
open import Foundation.Relation.Nullary.Negation public
open import Foundation.Relation.Nullary.Decidable public
open import Foundation.Relation.Nullary.Discrete public

open import Foundation.Relation.Unary.Countable public
open import Foundation.Relation.Unary.Enumerable as E public
open E.ListView public
```

> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Essential.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.essential)  
> 交流Q群: 893531731
