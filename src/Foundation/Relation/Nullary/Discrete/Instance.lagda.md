---
url: foundation.discrete.instance
---

# 元语言 ▸ 离散性 ▸ 实例

本章建立了一些基本类型的离散性. 我们从 `Foundation` 和标准库中导入了相关定义和引理.

```agda
module Foundation.Relation.Nullary.Discrete.Instance where

open import Foundation.Prelude
open import Foundation.Data.Maybe
open import Foundation.Data.Sigma
open import Foundation.Data.Sum
open import Foundation.Data.Vec
open import Foundation.Data.Vec.SetTheoretic
open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete.Base

import Data.Nat as ℕ
import Data.Product.Properties as Σ
import Data.Sum.Properties as ⊎
import Data.Maybe.Properties as ？
```

**<u>实例</u>** 自然数是离散的.  
**<u>证明</u>** 见标准库 [`ℕ._≟_`](https://agda.github.io/agda-stdlib/v1.7.3/Data.Nat.Properties.html#2538). ∎

```agda
instance
  discreteℕ : discrete ℕ
  discreteℕ = ℕ._≟_ _ _
```

**<u>实例</u>** 如果 `A` 和 `B` 是离散的, 那么 `A × B`, `A ⊎ B` 和 `A ？` 都是离散的.  
**<u>证明</u>** 见标准库 [`Σ.≡-dec`](https://agda.github.io/agda-stdlib/v1.7.3/Data.Product.Properties.html#1259), [`⊎.≡-dec`](https://agda.github.io/agda-stdlib/v1.7.3/Data.Sum.Properties.html#969) 和 [`？.≡-dec`](https://agda.github.io/agda-stdlib/v1.7.3/Data.Maybe.Properties.html#1037). ∎

```agda
  discrete× : ⦃ discrete A ⦄ → ⦃ discrete B ⦄ → discrete (A × B)
  discrete× = Σ.≡-dec _≟_ _≟_ _ _

  discrete⊎ : ⦃ discrete A ⦄ → ⦃ discrete B ⦄ → discrete (A ⊎ B)
  discrete⊎ = ⊎.≡-dec _≟_ _≟_ _ _

  discreteMaybe : ⦃ discrete A ⦄ → discrete (A ？)
  discreteMaybe = ？.≡-dec _≟_ _ _
```

与上面类似地, 标准库有向量的离散性的证明 [`𝕍.≡-dec`](https://agda.github.io/agda-stdlib/v1.7.3/Data.Vec.Properties.html#1789). 但我们证明一个更强的形式.

**<u>引理</u>** 对任意类型相同的向量 `x⃗` 和 `y⃗`, `x⃗ ≡ y⃗` 可判定, 只要对任意 `x ∈ x⃗` 和任意 `y`, `x ≡ y` 可判定.  
**<u>递归证明</u>** 对向量的长度归纳. 当它们都是空向量时判定为相等. 当它们的长度是 `suc n` 时, 即具有 `x ∷ x⃗` 和 `y ∷ y⃗` 的形式. 由于 `x ∈ x ∷ x⃗`, 由前提, 我们可以判定 `x ≡ y`. 又 `x⃗` 和 `y⃗` 具有长度 `n`, 由归纳假设, 可以判定 `x⃗ ≡ y⃗`. 由这两个判定的结果判定 `x ∷ x⃗` 是否等于 `y ∷ y⃗` 即可. ∎

```agda
discrete𝕍-strong : {n : ℕ} (x⃗ y⃗ : 𝕍 A n) → (∀ x → x ∈ x⃗ → ∀ y → Dec (x ≡ y)) → Dec (x⃗ ≡ y⃗)
discrete𝕍-strong [] [] H = yes refl
discrete𝕍-strong (x ∷ x⃗) (y ∷ y⃗) H with H x (here refl) y | discrete𝕍-strong x⃗ y⃗ (λ x x∈ y → H x (there x∈) y)
... | yes refl | yes refl = yes refl
... | yes refl | no ¬eq   = no $ ¬eq ∘ ∷-injectiveʳ
... | no ¬eq   | _        = no λ { refl → ¬eq refl }
```

**<u>实例</u>** 如果 `A` 是离散的, 那么 `𝕍 A n` 也是离散的.  
**<u>证明</u>** 由 `discrete𝕍-strong` 即得. ∎

```agda
instance
  discrete𝕍 : {n : ℕ} → ⦃ discrete A ⦄ → discrete (𝕍 A n)
  discrete𝕍 = discrete𝕍-strong _ _ λ _ _ _ → it
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Nullary/Discrete/Instance.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Relation.Nullary.Discrete.Instance.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.discrete.instance)  
> 交流Q群: 893531731
