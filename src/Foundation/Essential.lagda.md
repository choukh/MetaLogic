---
url: foundation.essential
---

# 元语言

> 交流Q群: 893531731  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Essential.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.essential)

## 前言

我们的研究对象是一阶逻辑等形式语言, 我们将其称为对象语言. 同时, 为了表达有关对象语言的命题和证明, 我们需要一个不同于对象语言的外部语言, 这个外部语言称为元语言. 传统上, 一阶逻辑等的元语言通常采用原始递归算术 (PRA) 等“低级”算术语言. 这主要是出于建立自下而上的逻辑体系以及满足有限主义哲学需求的考虑. 然而, 我们这里并不考虑这些因素, 而是采用一种称为[同伦类型论 (HoTT)](https://www.bananaspace.org/wiki/%E5%90%8C%E4%BC%A6%E7%B1%BB%E5%9E%8B%E8%AE%BA) 的“高级”语言作为元语言. 由于 HoTT 是一种更贴近数学实践的形式语言, 我们认为它可以在一定程度上兼顾形式上的严格与表达上的自然, 从而使完全形式化的入门讲义成为可能, 这也是我们的目标.

需要注意的是, HoTT 实际上是一系列理论的统称, 就像“集合论”有 ZFC, NBG, MK 等等一样. 本文具体使用的 HoTT 叫做 [Cubical Agda](https://agda.readthedocs.io/en/v2.6.4/language/cubical.html). 它非常严格, 以至于可以通过计算机来检查证明语句的正确性. 实际上它就是一种编程语言, 只不过其生态注重于数学证明而非软件应用. 借助 [Agda 的文学编程](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) 功能, [本 Markdown 文件](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Essential.lagda.md) 实际上就是 Agda 源码, 可以直接做类型检查, 以检验证明语句的正确性. 基于这一特性, 我们实验性地采用以下编排方式: 自然语言与代码级的形式语言并行使用, 交替排列, 构成双重元语言, 以构筑对象语言. 我们会将 Agda 语句放在代码块中, 而正文的自然语言则可以认为是对这些代码的注释. 我们希望两种元语言可以相互解释, 互为补充.

当然, 这要求读者对 HoTT 和 Agda 都有一定的了解. 我们不会在本文中对这些内容进行详细的介绍, 而是假设读者已经具备了一定的基础. 如果读者对 HoTT 和 Agda 还不熟悉, 我们推荐读者阅读以下资料:

- HoTT入门: [HoTT Book](https://homotopytypetheory.org/book/)
- Agda + 泛等基础入门: [Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
- 中文版快速参考: [Agda 泛等基础](https://www.yuque.com/ocau/hset/ti2u9nvok36hmibm)

## 基础概念

以下统一列出元语言中可以谈论的基础概念, 正篇中将直接使用它们而不再额外定义. 简单来说, 它们只不过是对 [Cubical 标准库](https://github.com/agda/cubical) 的重新封装, 以满足我们的特殊需求: 尽可能使用命题相等 (propositional equality) 而不是道路 (path), 以方便我们的形式化, 因为我们不涉及高阶同伦概念.

```agda
module Foundation.Essential where
```

### 前奏

前奏是基础中的基础, 是定义其他基础概念所必须的基础概念, 以至于有些是原始概念. 具体涉及到 Cubical 类型论的规则, 这里不深入其引入细节, 而只作为一个黑盒使用.

```agda
open import Foundation.Prelude public
```

具体地, 我们有以下前奏:

#### 内置

内置 (builtin) 模块主要包括有编译器支持的一些原始概念.

#### 函数

#### 命题相等

#### 同伦层级

#### 其他

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
