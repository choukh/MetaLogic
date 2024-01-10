---
url: fol.henkin
---

# 一阶逻辑 ▸ 亨金扩张

```agda
open import Foundation.Essential
open import FOL.Language
module FOL.HenkinExtension (ℒ : Language) where

open import FOL.Syntax.Base ℒ
open import FOL.Syntax.FreshVariables ℒ
```

```agda
record Input : 𝕋₁ where
  field
    𝒯 : Theory
    𝒯-closed : ∀ φ → 𝒯 φ holds → closed φ
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/FOL/HenkinExtension.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/FOL.HenkinExtension.html) | [语雀](https://www.yuque.com/ocau/metalogic/fol.henkin)  
> 交流Q群: 893531731
