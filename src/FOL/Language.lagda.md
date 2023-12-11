---
url: fol.language
---

# 一阶逻辑 ▸ 语言

一阶逻辑是一种形式语言, 其语句由一些原始符号按一定的语法组合而成. 符号又分为逻辑符号和非逻辑符号. 本篇先讲非逻辑符号.

非逻辑符号分为函数符号和关系符号, 且它们都带有一个称为元数 (arity) 的属性. 例如, 元数为 2 的函数符号即用于表示二元函数. 特别地, 元数为零的函数又称为常量.

较传统的处理方式是给出所有可能的函数符号和关系符号. 即对任意元数 $n$, 都有自然数多个函数符号

$$f^n_0,\ f^n_1,\ f^n_2,\ f^n_3,\ ...$$

以及自然数多个关系符号

$$R^n_0,\ R^n_1,\ R^n_2,\ R^n_3,\ ...$$

在这种处理下, 只有唯一一种一阶逻辑语言.

较现代的方式是根据最终要实现的一阶逻辑语言来指定该理论所需的非逻辑符号. 这些特定的符号以及它们的元数所组成的资料叫做理论的**签名 (signature)**. 在这种处理下, 每种签名都对应一种一阶逻辑语言, 因此签名又叫做**语言 (language)**, 语言的实例按惯例记作 ℒ. 由于一阶逻辑的其他部分都是参数化到语言的, 我们把它单独作为一个模块.

```agda
-- 元语言的基本概念
open import Foundation.Essential
-- 可枚举性的相关概念
open import Enumerability.ListView

module FOL.Language where
```

**<u>定义</u>** 一阶逻辑的语言 `ℒ` 是一个六元组

1. 离散的函数符号集 `𝓕`
2. 离散的关系符号集 `𝓡`
3. `𝓕` 到元数的映射 `∣_∣ᶠ`
4. `𝓡` 到元数的映射 `∣_∣ᴿ`
5. `𝓕` 的一个枚举
6. `𝓡` 的一个枚举

```agda
record Language : 𝕋₁ where
  constructor mkLang
  field
    𝓕 : 𝕋
    𝓡 : 𝕋
    ∣_∣ᶠ : 𝓕 → ℕ
    ∣_∣ᴿ : 𝓡 → ℕ
    discr𝓕 : discrete 𝓕
    discr𝓡 : discrete 𝓡
    ⦃ enum𝓕 ⦄ : Enum 𝓕
    ⦃ enum𝓡 ⦄ : Enum 𝓡
```

**<u>注意</u>** 在经典语境下集合一定是离散的, 但在直觉主义 HoTT 中, 离散强于“集合”. 因此当我们要求某 `A` 是“离散集”的时候, 实际上只要求它是离散类型, 然后它自然是一个集合.

**<u>注意</u>** 回顾[枚举的定义](https://www.yuque.com/ocau/metalogic/foundation.essential#c1933822), 某类型 `A` 的枚举 `Enum A`是一个二元组:
1. 满足 `wit` 的一个函数 `enum`
2. `enum` 的一个 `cum`

**<u>约定</u>** 对于一个类型, 我们自始至终只会谈论它的一个枚举. 所以对任意类型的枚举, 我们都会用 `enum`, `wit` 和 `cum` 来指代该类型的那个我们唯一谈论的枚举的 `enum`, `wit` 和 `cum`. 我们通过把 `enum𝓕` 放到括号 `⦃ ⦄` 中来声明它是我们唯一谈论的那个 `Enum 𝓕`. 对于 `enum𝓡` 也一样.

**<u>定理</u>** `𝓕` 和 `𝓡` 都是可数集.

```agda
  count𝓕 : countable 𝓕
  count𝓕 = discr→enum→count discr𝓕 ∣ enum𝓕 ∣₁

  count𝓡 : countable 𝓡
  count𝓡 = discr→enum→count discr𝓡 ∣ enum𝓡 ∣₁

  isSet𝓕 : isSet 𝓕
  isSet𝓕 = discrete→isSet discr𝓕

  isSet𝓡 : isSet 𝓡
  isSet𝓡 = discrete→isSet discr𝓡
```

**<u>例</u>** 下面给出了语言的一个实例 `ℒ`, 它可以作为皮亚诺算术的语言.

```agda
private module ExampleLanguagePA where

  data 𝓕 : 𝕋 where
    O : 𝓕
    S : 𝓕
    + : 𝓕
    * : 𝓕

  data 𝓡 : 𝕋 where
    < : 𝓡

  ∣_∣ᶠ : 𝓕 → ℕ
  ∣ O ∣ᶠ = 0
  ∣ S ∣ᶠ = 1
  ∣ + ∣ᶠ = 2
  ∣ * ∣ᶠ = 2

  ∣_∣ᴿ : 𝓡 → ℕ
  ∣ < ∣ᴿ = 2
```

通过模式匹配不难证明归纳定义的 `𝓕` 和 `𝓡` 是离散且可枚举的.

```agda
  discr𝓕 : discreteⓂ 𝓕
  discr𝓕 O O = yes refl
  discr𝓕 S S = yes refl
  discr𝓕 + + = yes refl
  discr𝓕 * * = yes refl
  discr𝓕 O S = no λ ()
  discr𝓕 O + = no λ ()
  discr𝓕 O * = no λ ()
  discr𝓕 S O = no λ ()
  discr𝓕 S + = no λ ()
  discr𝓕 S * = no λ ()
  discr𝓕 + O = no λ ()
  discr𝓕 + S = no λ ()
  discr𝓕 + * = no λ ()
  discr𝓕 * O = no λ ()
  discr𝓕 * S = no λ ()
  discr𝓕 * + = no λ ()

  discr𝓡 : discreteⓂ 𝓡
  discr𝓡 < < = yes refl

  enum𝓕 : Enum 𝓕
  enum𝓕 = mkEnum (λ _ → O ∷ S ∷ + ∷ [ * ]) (λ _ → [] , refl)
    λ { O → ex 0 (here refl)
      ; S → ex 0 (there (here refl))
      ; + → ex 0 (there (there (here refl)))
      ; * → ex 0 (there (there (there (here refl)))) }

  enum𝓡 : Enum 𝓡
  enum𝓡 = mkEnum (λ _ → < ∷ []) (λ _ → [] , refl)
    λ { < → ex 0 (here refl) }
```

于是它们可以构成语言.

```agda
  ℒ : Language
  ℒ = record
    { 𝓕 = 𝓕
    ; 𝓡 = 𝓡
    ; ∣_∣ᶠ = ∣_∣ᶠ
    ; ∣_∣ᴿ = ∣_∣ᴿ
    ; discr𝓕 = discr𝓕 _ _
    ; discr𝓡 = discr𝓡 _ _
    ; enum𝓕 = enum𝓕
    ; enum𝓡 = enum𝓡
    }
```

**<u>约定</u>** 我们一次只会谈论一种语言, 它在上下文中是明确的, 首次出现时会放在括号 `⦃ ⦄` 中或使用 `instance` 关键字来声明, 所以每次提到语言中的概念时不会一一带上某语言 `ℒ` 作为参数, 从而精简表达. 该约定表达为以下代码.

```agda
open Language ⦃...⦄ public
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Language.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Language.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.language)  
> 交流Q群: 893531731
