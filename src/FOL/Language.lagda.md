---
url: fol.language
---

# 一阶逻辑: 语言

> 交流Q群: 893531731  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Language.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Language.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.language)

```agda
module FOL.Language where

open import Foundation.Essential

record Language : 𝕋₁ where
  field
    𝓕 : 𝕋
    𝓡 : 𝕋
    ∣_∣ᶠ : 𝓕 → ℕ
    ∣_∣ᴿ : 𝓡 → ℕ
    discr𝓕 : discrete 𝓕
    discr𝓡 : discrete 𝓡
    enum𝓕 : enumerable 𝓕
    enum𝓡 : enumerable 𝓡

  count𝓕 : countable 𝓕
  count𝓕 = discr→enum→count discr𝓕 enum𝓕

  count𝓡 : countable 𝓡
  count𝓡 = discr→enum→count discr𝓡 enum𝓡

  isSet𝓕 : isSet 𝓕
  isSet𝓕 = discrete→isSet discr𝓕

  isSet𝓡 : isSet 𝓡
  isSet𝓡 = discrete→isSet discr𝓡
```
