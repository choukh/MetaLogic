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
open import Foundation.Data.Vec
open import Foundation.Data.Vec.SetTheoretic
open import Foundation.Relation.Nullary.Decidable
open import Foundation.Relation.Nullary.Discrete.Base

import Data.Nat as ℕ
import Cubical.Data.Maybe as 🧊
import Cubical.Data.Sum as 🧊

open import Data.Product.Properties
  using ()
  renaming (≡-dec to discreteΣ)

private variable
  n : ℕ

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

```agda
discrete𝕍-strong : (x⃗ y⃗ : 𝕍 A n) → (∀ x → x ∈ x⃗ → ∀ y → Dec (x ≡ y)) → Dec (x⃗ ≡ y⃗)
discrete𝕍-strong [] [] H = yes refl
discrete𝕍-strong (x ∷ x⃗) (y ∷ y⃗) H with H x (here refl) y | discrete𝕍-strong x⃗ y⃗ (λ x x∈ y → H x (there x∈) y)
... | yes refl | yes refl = yes refl
... | yes refl | no ¬eq   = no $ ¬eq ∘ ∷-injectiveʳ
... | no ¬eq   | _        = no λ { refl → ¬eq refl }
```

```agda
instance
  discrete𝕍 : ⦃ discrete A ⦄ → discrete (𝕍 A n)
  discrete𝕍 = discrete𝕍-strong _ _ λ _ _ _ → it
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Nullary/Discrete/Instance.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Relation.Nullary.Discrete.Instance.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.discrete.instance)  
> 交流Q群: 893531731
