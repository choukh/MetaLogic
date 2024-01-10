---
url: foundation.discrete.base
---

# 元语言 ▸ 离散性 ▸ 定义

离散性是类型具有的一种属性, 是直觉主义中特有的一种概念, 其定义依赖于可判定性 `Dec`.

```agda
module Foundation.Relation.Nullary.Discrete.Base where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Decidable
```

标准库和Cubical库中都有离散性的定义, 我们把标准库中的叫做 `discreteⓢ`, 而把Cubical库中的叫做 `discrete🧊`. 除了形式上的微小差异, 它们大体上是等价的. 我们将建立它们之间的联系.

```agda
open import Relation.Binary public
  using ()
  renaming (DecidableEquality to discreteⓢ)

open import Cubical.Relation.Nullary as 🧊
  using ()
  renaming (
    Discrete to discrete🧊;
    Discrete→isSet to discrete🧊→isSet🧊
  )
```

**<u>定义</u>** 我们说一个类型是离散的, 当且仅当它的任意两个元素的相等都是可判定的.

```agda
discrete : 𝕋 ℓ → 𝕋 ℓ
discrete A = {x y : A} → Dec (x ≡ y)
```

该定义与标准库中的 `discreteⓢ` 相比只是多了参数的隐式化. 这主要是出于实用上的考虑, 我们希望类型的离散性能被声明为[**实例 (instance)**](https://agda.readthedocs.io/en/v2.6.4.1/language/instance-arguments.html), 而这要求定义中不带任何显式参数.

以下函数建立了两种定义的联系, 实际上就是把隐参显式化了. 对于已经声明了实例的离散类型, 我们可以通过调用 `x ≟ y` 判定 `x` 是否等于 `y`.

```agda
_≟_ : ⦃ discrete A ⦄ → discreteⓢ A
_≟_ _ _ = it
```

我们的定义与Cubical库中的定义也是逻辑等价的.

```agda
discrete→🧊 : discrete A → discrete🧊 A
discrete→🧊 H _ _ = Dec→🧊 $ subst Dec (sym Eq≡🧊) H

discrete←🧊 : discrete🧊 A → discrete A
discrete←🧊 H {x} {y} = Dec←🧊 $ subst 🧊.Dec Eq≡🧊 (H x y)
```

**<u>引理</u>** 如果一个类型是集合, 那么它的离散性是一个命题.  
**<u>证明</u>** 由可判定性的命题性即得. ∎

```agda
isPropDiscrete : isSet A → isProp (discrete A)
isPropDiscrete H = isPropΠ̅2 λ x y → isPredDec (H x y)
```

**<u>引理</u>** 如果一个类型是离散的, 那么它是一个集合.
**<u>证明</u>** 见Cubical库 [`Discrete→isSet`](https://agda.github.io/cubical/Cubical.Relation.Nullary.Properties.html#6952). ∎

```agda
discreteSet : ⦃ discrete A ⦄ → isSet A
discreteSet = isSet←🧊 $ discrete🧊→isSet🧊 $ discrete→🧊 it
```

**<u>注意</u>** 在经典语境下集合一定是离散的, 但在直觉主义 HoTT 中, 离散强于“集合”. 因此当我们要求某 `A` 是“离散集”的时候, 实际上只要求它是离散类型, 然后它自然是一个集合.

**<u>约定</u>** 对于已经确立了离散性的类型, 我们直接把它当作集合来看待. 代码上是把离散性的证据放到括号 `⦃ ⦄` 中来声明, 并且统一使用 `discreteSet` 来说明这些被声明的离散类型是集合.

**<u>定义</u>** 离散类型所组成的宇宙叫做离散集合宇宙, 记作 `𝔻 ℓ`, 也叫经典集合宇宙, 其中的类型都是集合.

```agda
𝔻 : ∀ ℓ → 𝕋 (ℓ ⁺)
𝔻 ℓ = TypeWithStr ℓ discrete

𝔻₀ : 𝕋₁
𝔻₀ = 𝔻 ℓ0

isSetTyp𝔻 : {𝗔 : 𝔻 ℓ} → isSet (typ 𝗔)
isSetTyp𝔻 {𝗔} = discreteSet ⦃ str 𝗔 ⦄
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Nullary/Discrete/Base.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Relation.Nullary.Discrete.Base.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.discrete.base)  
> 交流Q群: 893531731
