---
url: foundation.essential
---

# 元语言

## 前言

我们的研究对象是一阶逻辑等形式语言, 我们将其称为对象语言. 同时, 为了表达有关对象语言的命题和证明, 我们需要一个不同于对象语言的外部语言, 这个外部语言称为元语言. 传统上, 一阶逻辑等的元语言通常采用原始递归算术 (PRA) 等“低级”算术语言. 这主要是出于建立自下而上的逻辑体系以及满足有限主义哲学需求的考虑. 然而, 我们这里并不考虑这些因素, 而是采用一种称为[同伦类型论 (HoTT)](https://www.bananaspace.org/wiki/%E5%90%8C%E4%BC%A6%E7%B1%BB%E5%9E%8B%E8%AE%BA) 的“高级”语言作为元语言. 由于 HoTT 是一种更贴近数学实践的形式语言, 我们认为它可以在一定程度上兼顾形式上的严格与表达上的自然, 从而使完全形式化的入门讲义成为可能, 这也是我们的目标.

需要注意的是, HoTT 实际上是一系列理论的统称, 就像“集合论”有 ZFC, NBG, MK 等等一样. 本文具体使用的 HoTT 叫做 [Cubical Agda](https://agda.readthedocs.io/en/v2.6.4/language/cubical.html). 它非常严格, 以至于可以通过计算机来检查证明语句的正确性. 实际上它就是一种编程语言, 只不过其生态注重于数学证明而非软件应用. 借助 [Agda 的文学编程](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) 功能, [本 Markdown 文件](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) 实际上就是 Agda 源码, 可以直接做类型检查, 以检验证明语句的正确性. 基于这一特性, 我们实验性地采用以下编排方式: 自然语言与代码级的形式语言并行使用, 交替排列, 构成双重元语言, 以构筑对象语言. 我们会将 Agda 语句放在代码块中, 而正文的自然语言则可以认为是对这些代码的注释. 我们希望两种元语言可以相互解释, 互为补充.

当然, 这要求读者对 HoTT 和 Agda 都有一定的了解. 我们不会在本文中对这些内容进行详细的介绍, 而是假设读者已经具备了一定的基础. 如果读者对 HoTT 和 Agda 还不熟悉, 我们推荐读者阅读以下资料:

- HoTT入门: [HoTT Book](https://homotopytypetheory.org/book/)
- Agda + 泛等基础入门: [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
- 中文版快速参考: [Agda 泛等基础](https://www.yuque.com/ocau/hset/ti2u9nvok36hmibm)

## 基础概念

以下统一列出元语言中可以谈论的基础概念, 正篇中将直接使用它们而不再额外定义. 简单来说, 它们只不过是对 [Cubical 标准库](https://github.com/agda/cubical) 的重新封装, 以满足我们的特殊需求: 尽可能使用命题相等 (Propositional Equality) 而不是道路 (Path), 以方便我们的形式化, 因为我们不涉及高阶同伦概念.

```agda
module Foundation.Essential where
```

### 前奏

前奏 (Prelude) 是基础中的基础, 是定义其他基础概念所必须的基础概念, 以至于有些是原始概念, 如道路类型. 这些原始概念具体涉及到 Cubical 类型论的规则, 这里不深入其细节, 而只作为一个黑盒使用.

#### 内置

```agda
open import Foundation.Prelude.Builtin public
```

内置 (Builtin) 模块主要包括带编译器支持的一些原始概念, 如宇宙和道路类型等, 以及一些基本数据类型:

- 宇宙: 类型宇宙 `𝕋`, 宇宙层级 `Level`, 零级宇宙 `0ℓ`, 后继宇宙 `_⁺`, 宇宙二元并 `_⊔_`, 宇宙提升 `Lift`
- 同一性类型: 命题相等类型 `_≡_`, 道路类型 `_≡🧊_`
- 基本数据类型: 单元类型 `⊤`, 布尔类型 `𝔹`, 自然数类型 `ℕ`, 列表 (有序不定长有限集合) 类型 `𝕃`, Σ类型 `Σ`

注意, 对某些相似概念的 Cubical 版本, 我们会在其名字中带上“🧊”, 以示区别. 此外, 我们对符号作如下约定:

- 宇宙层级编号: `ℓ ℓ′ ℓ″ ℓ‴ ℓ⁗ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level`
- 位于任意宇宙的类型: `A B C D T : 𝕋 ℓ`
- 类型族 / 一元关系: `P Q : A → 𝕋 ℓ`
- 二元关系: `R S : A → B → 𝕋 ℓ`
- 依值类型族: `P₂ Q₂ : (x : A) → P x → 𝕋 ℓ`

注意当我们说“任意”的时候指的是 arbitrary, 而对于 forall, 我们一定会说“所有”或“对任意”. 我们保留“谓词”这个名称给可以证明是命题的一元关系. 最后, 我们约定Σ类型 `Σ A (λ x → P)`, 即满足 `P` 的 `A`, 可以简记为 `Σ x ꞉ A ⸴ P`, 或者 `Σ x ⸴ P`.

#### 函数

```agda
open import Foundation.Prelude.Function public
```

前奏中的函数模块主要定义与函数有关的一些便利记法:

- 恒等函数构造函数 `id = λ x → x`
- 恒等函数一元关系 `isId = λ f → ∀ x y → f x ≡ f y`
- 一元函数复合 `f ∘ g = λ x → f (g x)`
- 一元-二元函数复合 `f ∘₂ g = λ x y → f (g x y)`
- 一元-三元函数复合 `f ∘₃ g = λ x y z → f (g x y z)`
- 二元函数参数翻转 `flip = λ f x y → f y x`
- 函数应用 `f $ x = f x`, 用于当参数本身是个函数应用时省略参数外层的括号

#### 命题相等

```agda
open import Foundation.Prelude.Equality public
```

#### 同伦层级

```agda
open import Foundation.Prelude.HLevel public
```

#### 其他

```agda
open import Foundation.Prelude.Misc public
```

### 逻辑

```agda
open import Foundation.Logic public
```

### 集合

```agda
open import Foundation.Set.Powerset public
```

### 函数

```agda
open import Foundation.Function.Bundles public
open import Foundation.Function.Sequance public
```

### 数据类型

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

### 关系

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
