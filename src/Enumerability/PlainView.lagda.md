---
url: foundation.enumerability.plainview
---

# 可枚举性 ▸ 普通视角

```agda
module Enumerability.PlainView where
import Enumerability.ListView.Base as Ⓛ

open import Foundation.Essential
open import Foundation.Data.Nat.AlternativeOrder

record Enum (A : 𝕋 ℓ) : 𝕋 (ℓ ⁺) where
  field
    ⦃ enumⓁ ⦄ : Ⓛ.Enum A
    discr : discrete A
    Hₗ : ∀ n → length (Ⓛ.enum n) > n

  enum : ℕ → A
  enum n = Σ[<length]? (Ⓛ.enum n) (Hₗ n) .fst
```

---
> 知识共享许可协议: [CC-BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/deed.zh)  
> [GitHub](https://github.com/choukh/MetaLogic/blob/main/src/Enumerability/PlainView.lagda.md) | [GitHub Pages](https://choukh.github.io/MetaLogic/Enumerability.PlainView.html) | [语雀](https://www.yuque.com/ocau/metalogic/enumerability.plainview)  
> 交流Q群: 893531731
