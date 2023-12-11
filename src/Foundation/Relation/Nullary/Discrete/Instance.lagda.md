---
url: foundation.discrete.instance
---

# 元语言 ▸ 离散性 ▸ 实例

```agda
module Foundation.Relation.Nullary.Discrete.Instance where

open import Foundation.Prelude
open import Foundation.Data.Maybe
open import Foundation.Data.Sigma
open import Foundation.Data.Sum
open import Foundation.Relation.Nullary.Discrete.Base

import Data.Nat as ℕ
import Cubical.Data.Maybe as 🧊
import Cubical.Data.Sum as 🧊

open import Data.Product.Properties
  using ()
  renaming (≡-dec to discreteΣ)

instance

  discreteℕ : discrete ℕ
  discreteℕ = ℕ._≟_ _ _

  discrete× : ⦃ discrete A ⦄ → ⦃ discrete B ⦄ → discrete (A × B)
  discrete× = discreteΣ (λ _ _ → it) (λ _ _ → it) _ _

  discreteMaybe : ⦃ discrete A ⦄ → discrete (A ？)
  discreteMaybe = subst discrete Maybe≡🧊 $
    discrete←🧊 $ 🧊.discreteMaybe $ discrete→🧊 it

  discrete⊎ : ⦃ discrete A ⦄ → ⦃ discrete B ⦄ → discrete (A ⊎ B)
  discrete⊎ = subst discrete Sum≡🧊 $
    discrete←🧊 $ 🧊.discrete⊎ (discrete→🧊 it) (discrete→🧊 it)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Nullary/Discrete/Instance.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Relation.Nullary.Discrete.Instance.html) | [语雀](https://www.yuque.com/ocau/metalogic/discrete.instance)  
> 交流Q群: 893531731
