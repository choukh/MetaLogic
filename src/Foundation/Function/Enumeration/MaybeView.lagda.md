---
url: foundation.enumeration.maybeview
---

# 元语言 ▸ 可枚举性 ▸ 可选值序列视角

我们一共引入枚举的三种视角， 分别是：

1. 可选值序列视角 (本篇): 与传统定义接轨, 但不会实际使用. 与视角2等价, 可以说明视角2的合理性.
2. [累积列表视角](https://www.yuque.com/ocau/metalogic/foundation.enumeration.listview.base): 是我们实际构造的枚举函数.
3. [普通视角](https://www.yuque.com/ocau/metalogic/foundation.enumeration.plainview): 是我们证明命题时实际使用的枚举函数, 从视角2转化.

我们首先介绍可选值序列视角, 也就是传统的枚举定义.

```agda
module Foundation.Function.Enumeration.MaybeView where

open import Foundation.Prelude
open import Foundation.Prop.Logic
open import Foundation.Prop.Iff
open import Foundation.Prop.Truncation
open import Foundation.Function.Bijection

open import Foundation.Data.Maybe
open import Foundation.Data.Nat.ConstructiveEpsilon
open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete.Base
open import Foundation.Relation.Nullary.Discrete.Instance
open import Foundation.Relation.Unary.Countable
```

**<u>定义</u>** `x : A` 在可选值序列 `f : ℕ → A ？` 中的见证集, 记作 `Witness f x`, 定义为满足 `f n ≡ some x` 的所有 `n` (称为 `x` 的见证) 组成的集合.

```agda
Witness : (ℕ → A ？) → A → 𝕋 _
Witness f x = Σ n ， f n ≡ some x
```

**<u>定义</u>** 我们说 `f` 见证了 `x`, 记作 `f witness x`, 当且仅当见证集 `Witness f x` 有值, 也即存在 `x` 的见证.

```agda
_witness_ : (ℕ → A ？) → A → 𝕋 _
f witness x = ∥ Witness f x ∥₁
```

**<u>定义</u>** 见证了所有 `x : A` 的 `f` 构成了 `A` 的一个枚举, 记作 `Enum f`.

```agda
Enum : 𝕋 ℓ → 𝕋 _
Enum A = Σ f ， ∀ (x : A) → f witness x
```

**<u>定义</u>** 当且仅当 `P x` 成立时会见证 `x` 的 `f` 构成了满足 `P` 的那些 `x : A` 的一个枚举, 简称 `P` 的一个枚举, 记作 `Enumℙ P`.

```agda
Enumℙ : (A → 𝕋 ℓ) → 𝕋 _
Enumℙ P = Σ f ， ∀ x → P x ↔ f witness x
```

当 `P` 是恒真性质时, 以上两种枚举可以相互转化.

```agda
Enum↔ℙ : Enum A ↔ Enumℙ λ (_ : A) → ⊤
Enum↔ℙ = ⇒: (λ (f , H) → f , λ x → ⇒: (λ _ → H x) ⇐: (λ _ → tt))
         ⇐: (λ (f , H) → f , λ x → H x .⇒ tt)
```

**<u>定义</u>** 我们说 `A` 递归可枚举, 当且仅当存在 `A` 的一个枚举.

```agda
enumerable : 𝕋 ℓ → 𝕋 _
enumerable A = ∥ Enum A ∥₁
```

**<u>定义</u>** 我们说 `P` 递归可枚举, 当且仅当存在 `P` 的一个枚举.

```agda
enumerableℙ : (A → 𝕋 ℓ) → 𝕋 _
enumerableℙ P = ∥ Enumℙ P ∥₁
```

当 `P` 是恒真性质时, 以上两种递归可枚举性等价.

```agda
enumerable↔ℙ : enumerable A ↔ enumerableℙ λ (_ : A) → ⊤
enumerable↔ℙ = ↔-map Enum↔ℙ
```

**<u>引理</u>** 如果 `f` 见证了整个离散集 `A`, 那么可以取到每个 `x : A` 的见证.  
**<u>证明</u>** 这是一个类似选择公理的形式, 自然数的良序性提供了“选择函数”, 即对每个 `x : A` 取最小的见证 `n` 即可. ∎

```agda
discr→wit→Wit : ⦃ discrete A ⦄ → {f : ℕ → A ？} → (∀ x → f witness x) → (∀ x → Witness f x)
discr→wit→Wit {f} wit x = ε sets discr (wit x) where
  sets : isSets (λ n → f n ≡ some x)
  sets n = isProp→isSet $ (isSetMaybe discreteSet) _ _
  discr : ∀ n → Dec (f n ≡ some x)
  discr n = it
```

**<u>事实</u>** 离散的递归可枚举集可数.  
**<u>证明</u>** 只需证 `A` 的枚举可以转化为 `A` 到 `ℕ` 的单射. 用 `discr→wit→Wit` 取每个 `x` 的见证 `n`, 将该映射记为 `g`, 它满足

`f∘g-wit : ∀ x → f (g x) ≡ some x`

我们证明 `g` 即是单射. 给定等式 `g x ≡ g y`, 则有 `f (g x) ≡ f (g y)`. 两边用 `f∘g-wit` 换成 `some` 形式, 再用 `some` 的单射性即得 `x ≡ y`. ∎

```agda
discr→enum→count : ⦃ discrete A ⦄ → enumerable A → countable A
discr→enum→count {A} = 𝟙.map H where
  H : Enum A → A ↣ ℕ
  H (f , f-wit) = g , g-inj where
    Wit : ∀ x → Witness f x
    Wit = discr→wit→Wit f-wit
    g : A → ℕ
    g = fst ∘ Wit
    f∘g-wit : ∀ x → f (g x) ≡ some x
    f∘g-wit = snd ∘ Wit
    g-inj : injective g
    g-inj {x} {y} eq = some-inj $
      some x   ≡˘⟨ f∘g-wit x ⟩
      f (g x)  ≡⟨ cong f eq ⟩
      f (g y)  ≡⟨ f∘g-wit y ⟩
      some y   ∎
```

**<u>事实</u>** 可数无穷集离散.  
**<u>证明</u>** 由于集合的离散性是命题, 可转化为证 `A ≅ ℕ → discrete A`, 于是可归结为 `ℕ` 的离散性. ∎

```agda
count∞→discr : isSet A → countablyInfinite A → discrete A
count∞→discr sA = 𝟙.rec (isPropDiscrete sA) H where
  H : A ≅ ℕ → discrete A
  H (mk≅ f f⁻¹ f∘f⁻¹ f⁻¹∘f) {x} {y} with f x ≟ f y
  ... | yes p = yes $ subst2 _≡_ (f⁻¹∘f _) (f⁻¹∘f _) (cong f⁻¹ p)
  ... | no ¬p = no λ { refl → ¬p refl }
```

**<u>事实</u>** 可数无穷蕴含递归可枚举.  
**<u>证明</u>** 即证与自然数集的同构可以转化为枚举. 同构给了我们互逆的 `f : A → ℕ` 和 `f⁻¹ : ℕ → A`. `some` 与 `f⁻¹` 的复合即是所需的枚举函数, `f x` 给出了 `x` 在 `some ∘ f⁻¹` 中的一个见证. ∎

```agda
count∞→enum : countablyInfinite A → enumerable A
count∞→enum {A} = 𝟙.map H where
  H : A ≅ ℕ → Enum A
  H (mk≅ f f⁻¹ f∘f⁻¹ f⁻¹∘f) = g , wit where
    g = some ∘ f⁻¹
    wit : ∀ x → g witness x
    wit x = ex (f x) (cong some (f⁻¹∘f x))
```

**<u>注意</u>** 由以上三个事实, 可以看出, 在我们的元语言中, 离散的递归可枚举集等价于可数集, 只要该可数集的基数被构造地给出. 此结果与经典不符, 原因在于经典的可数集不一定构造地给出了其基数.

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Function/Enumeration/MaybeView.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Function.Enumeration.MaybeView.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.enumeration.maybeview)  
> 交流Q群: 893531731
