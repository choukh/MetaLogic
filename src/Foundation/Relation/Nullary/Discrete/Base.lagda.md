---
url: foundation.discreteness.base
---

# 元语言 ▸ 离散性 ▸ 定义

```agda
module Foundation.Relation.Nullary.Discrete.Base where

open import Foundation.Prelude
open import Foundation.Relation.Nullary.Decidable

open import Relation.Binary public
  using ()
  renaming (DecidableEquality to discreteⓂ)

open import Cubical.Relation.Nullary as 🧊
  using ()
  renaming (
    Discrete to discrete🧊;
    Discrete→isSet to discrete🧊→isSet🧊
  )

discrete : 𝕋 ℓ → 𝕋 ℓ
discrete A = {x y : A} → Dec (x ≡ y)

_≟_ : ⦃ discrete A ⦄ → discreteⓂ A
_≟_ _ _ = it

discrete→🧊 : discrete A → discrete🧊 A
discrete→🧊 H _ _ = Dec→🧊 $ subst Dec (sym Eq≡🧊) H

discrete←🧊 : discrete🧊 A → discrete A
discrete←🧊 H {x} {y} = Dec←🧊 $ subst 🧊.Dec Eq≡🧊 (H x y)

discrete→isSet : ⦃ discrete A ⦄ → isSet A
discrete→isSet = isSet←🧊 $ discrete🧊→isSet🧊 $ discrete→🧊 it

isPropDiscrete : isSet A → isProp (discrete A)
isPropDiscrete H = isPropΠ̅2 λ x y → isPropDec (H x y)

𝔻 : ∀ ℓ → 𝕋 (ℓ ⁺)
𝔻 ℓ = TypeWithStr ℓ discrete

𝔻₀ : 𝕋₁
𝔻₀ = 𝔻 ℓ0

isSetTyp𝔻 : {𝗔 : 𝔻 ℓ} → isSet (typ 𝗔)
isSetTyp𝔻 {𝗔} = discrete→isSet ⦃ str 𝗔 ⦄
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Foundation/Relation/Nullary/Discrete/Base.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Foundation.Relation.Nullary.Discrete.Base.html) | [语雀](https://www.yuque.com/ocau/metalogic/foundation.discrete.base)  
> 交流Q群: 893531731
