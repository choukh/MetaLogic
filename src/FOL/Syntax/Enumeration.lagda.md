---
url: fol.syntax.enumeration
---

# 一阶逻辑 ▸ 语法 ▸ᐞ 公式的枚举

```agda
open import Foundation.Essential
open import FOL.Language

module FOL.Syntax.Enumeration
  (ℒ @ (mkLang 𝓕 𝓡 ∣_∣ᶠ ∣_∣ᴿ _ _ (eᶠ , cᶠ , wᶠ) (eᴿ , cᴿ , wᴿ)) : Language)
  where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
```

## 向量的枚举性

```agda
combine : 𝕃 A → (n : ℕ) → 𝕃 (𝕍 A n)
combine xs zero = [ [] ]
combine xs (suc n) = map (λ (x , x⃗) → x ∷ x⃗) (xs [×] combine xs n)
```

## 项的枚举

```agda
termLists : 𝕃ₙ Term
termLists zero = []
termLists (suc n) = termLists n ++ # n ∷ concat (map apps (eᶠ n)) where
  apps : 𝓕 → 𝕃 Term
  apps f = map (f $̇_) (combine (termLists n) ∣ f ∣ᶠ)
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/Syntax/Enumeration.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.Syntax.Enumeration.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.syntax.enumeration)  
> 交流Q群: 893531731
